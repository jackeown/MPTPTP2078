%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1723+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:17 EST 2020

% Result     : Theorem 6.63s
% Output     : CNFRefutation 6.63s
% Verified   : 
% Statistics : Number of formulae       :  239 (6294 expanded)
%              Number of clauses        :  172 (1734 expanded)
%              Number of leaves         :   17 (2099 expanded)
%              Depth                    :   28
%              Number of atoms          : 1205 (71165 expanded)
%              Number of equality atoms :  314 (2794 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   28 (   4 average)
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
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( m1_pre_topc(X2,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) )
                      & ( m1_pre_topc(X1,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) ) ) ) ) ) ) ) ),
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
                      & ~ v2_struct_0(X3) )
                   => ( ~ r1_tsep_1(X1,X2)
                     => ( ( m1_pre_topc(X2,X3)
                         => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) )
                        & ( m1_pre_topc(X1,X3)
                         => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
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
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
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
    inference(flattening,[],[f28])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
              & m1_pre_topc(X2,X3) )
            | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
              & m1_pre_topc(X1,X3) ) )
          & ~ r1_tsep_1(X1,X2)
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,sK3))
            & m1_pre_topc(X2,sK3) )
          | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,sK3,X2))
            & m1_pre_topc(X1,sK3) ) )
        & ~ r1_tsep_1(X1,X2)
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                  & m1_pre_topc(X2,X3) )
                | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                  & m1_pre_topc(X1,X3) ) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,sK2),k2_tsep_1(X0,X1,X3))
                & m1_pre_topc(sK2,X3) )
              | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,sK2),k2_tsep_1(X0,X3,sK2))
                & m1_pre_topc(X1,X3) ) )
            & ~ r1_tsep_1(X1,sK2)
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
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
                ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,sK1,X2),k2_tsep_1(X0,sK1,X3))
                    & m1_pre_topc(X2,X3) )
                  | ( ~ m1_pre_topc(k2_tsep_1(X0,sK1,X2),k2_tsep_1(X0,X3,X2))
                    & m1_pre_topc(sK1,X3) ) )
                & ~ r1_tsep_1(sK1,X2)
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                        & m1_pre_topc(X2,X3) )
                      | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
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
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X3,X2))
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

fof(f37,plain,
    ( ( ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
        & m1_pre_topc(sK2,sK3) )
      | ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f36,f35,f34,f33])).

fof(f63,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3) )
                    & ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)
                      | k2_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f39])).

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

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

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
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,
    ( m1_pre_topc(sK2,sK3)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f69,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f68,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1091,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1661,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1091])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1093,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1659,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1093])).

cnf(c_2,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(k2_tsep_1(X2,X0,X1),X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k2_tsep_1(X2,X0,X1))
    | ~ v1_pre_topc(k2_tsep_1(X2,X0,X1))
    | u1_struct_0(k2_tsep_1(X2,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1106,plain,
    ( r1_tsep_1(X0_46,X1_46)
    | ~ m1_pre_topc(X0_46,X2_46)
    | ~ m1_pre_topc(X1_46,X2_46)
    | ~ m1_pre_topc(k2_tsep_1(X2_46,X0_46,X1_46),X2_46)
    | ~ l1_pre_topc(X2_46)
    | v2_struct_0(X0_46)
    | v2_struct_0(X1_46)
    | v2_struct_0(X2_46)
    | v2_struct_0(k2_tsep_1(X2_46,X0_46,X1_46))
    | ~ v1_pre_topc(k2_tsep_1(X2_46,X0_46,X1_46))
    | u1_struct_0(k2_tsep_1(X2_46,X0_46,X1_46)) = k3_xboole_0(u1_struct_0(X0_46),u1_struct_0(X1_46)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1646,plain,
    ( u1_struct_0(k2_tsep_1(X0_46,X1_46,X2_46)) = k3_xboole_0(u1_struct_0(X1_46),u1_struct_0(X2_46))
    | r1_tsep_1(X1_46,X2_46) = iProver_top
    | m1_pre_topc(X2_46,X0_46) != iProver_top
    | m1_pre_topc(X1_46,X0_46) != iProver_top
    | m1_pre_topc(k2_tsep_1(X0_46,X1_46,X2_46),X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v2_struct_0(X1_46) = iProver_top
    | v2_struct_0(X2_46) = iProver_top
    | v2_struct_0(k2_tsep_1(X0_46,X1_46,X2_46)) = iProver_top
    | v1_pre_topc(k2_tsep_1(X0_46,X1_46,X2_46)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1106])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v1_pre_topc(k2_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1104,plain,
    ( ~ m1_pre_topc(X0_46,X1_46)
    | ~ m1_pre_topc(X2_46,X1_46)
    | ~ l1_pre_topc(X1_46)
    | v2_struct_0(X0_46)
    | v2_struct_0(X1_46)
    | v2_struct_0(X2_46)
    | v1_pre_topc(k2_tsep_1(X1_46,X2_46,X0_46)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1648,plain,
    ( m1_pre_topc(X0_46,X1_46) != iProver_top
    | m1_pre_topc(X2_46,X1_46) != iProver_top
    | l1_pre_topc(X1_46) != iProver_top
    | v2_struct_0(X2_46) = iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v2_struct_0(X1_46) = iProver_top
    | v1_pre_topc(k2_tsep_1(X1_46,X2_46,X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1104])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1103,plain,
    ( ~ m1_pre_topc(X0_46,X1_46)
    | ~ m1_pre_topc(X2_46,X1_46)
    | ~ l1_pre_topc(X1_46)
    | v2_struct_0(X0_46)
    | v2_struct_0(X1_46)
    | v2_struct_0(X2_46)
    | ~ v2_struct_0(k2_tsep_1(X1_46,X2_46,X0_46)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1649,plain,
    ( m1_pre_topc(X0_46,X1_46) != iProver_top
    | m1_pre_topc(X2_46,X1_46) != iProver_top
    | l1_pre_topc(X1_46) != iProver_top
    | v2_struct_0(X2_46) = iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v2_struct_0(X1_46) = iProver_top
    | v2_struct_0(k2_tsep_1(X1_46,X2_46,X0_46)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1103])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1105,plain,
    ( ~ m1_pre_topc(X0_46,X1_46)
    | ~ m1_pre_topc(X2_46,X1_46)
    | m1_pre_topc(k2_tsep_1(X1_46,X2_46,X0_46),X1_46)
    | ~ l1_pre_topc(X1_46)
    | v2_struct_0(X0_46)
    | v2_struct_0(X1_46)
    | v2_struct_0(X2_46) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1647,plain,
    ( m1_pre_topc(X0_46,X1_46) != iProver_top
    | m1_pre_topc(X2_46,X1_46) != iProver_top
    | m1_pre_topc(k2_tsep_1(X1_46,X2_46,X0_46),X1_46) = iProver_top
    | l1_pre_topc(X1_46) != iProver_top
    | v2_struct_0(X2_46) = iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v2_struct_0(X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1105])).

cnf(c_1905,plain,
    ( u1_struct_0(k2_tsep_1(X0_46,X1_46,X2_46)) = k3_xboole_0(u1_struct_0(X1_46),u1_struct_0(X2_46))
    | r1_tsep_1(X1_46,X2_46) = iProver_top
    | m1_pre_topc(X2_46,X0_46) != iProver_top
    | m1_pre_topc(X1_46,X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top
    | v2_struct_0(X2_46) = iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v2_struct_0(X1_46) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1646,c_1648,c_1649,c_1647])).

cnf(c_5145,plain,
    ( u1_struct_0(k2_tsep_1(sK0,X0_46,sK2)) = k3_xboole_0(u1_struct_0(X0_46),u1_struct_0(sK2))
    | r1_tsep_1(X0_46,sK2) = iProver_top
    | m1_pre_topc(X0_46,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1661,c_1905])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_33,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_35,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_38,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5791,plain,
    ( m1_pre_topc(X0_46,sK0) != iProver_top
    | r1_tsep_1(X0_46,sK2) = iProver_top
    | u1_struct_0(k2_tsep_1(sK0,X0_46,sK2)) = k3_xboole_0(u1_struct_0(X0_46),u1_struct_0(sK2))
    | v2_struct_0(X0_46) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5145,c_33,c_35,c_38])).

cnf(c_5792,plain,
    ( u1_struct_0(k2_tsep_1(sK0,X0_46,sK2)) = k3_xboole_0(u1_struct_0(X0_46),u1_struct_0(sK2))
    | r1_tsep_1(X0_46,sK2) = iProver_top
    | m1_pre_topc(X0_46,sK0) != iProver_top
    | v2_struct_0(X0_46) = iProver_top ),
    inference(renaming,[status(thm)],[c_5791])).

cnf(c_5801,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,sK2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | r1_tsep_1(sK3,sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1659,c_5792])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_40,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5848,plain,
    ( r1_tsep_1(sK3,sK2) = iProver_top
    | u1_struct_0(k2_tsep_1(sK0,sK3,sK2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5801,c_40])).

cnf(c_5849,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,sK2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | r1_tsep_1(sK3,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_5848])).

cnf(c_12,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X2,X0)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_579,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | sK0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_31])).

cnf(c_580,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_582,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_580,c_32,c_30])).

cnf(c_583,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_582])).

cnf(c_1083,plain,
    ( ~ r1_tsep_1(X0_46,X1_46)
    | r1_tsep_1(X1_46,X2_46)
    | ~ m1_pre_topc(X2_46,X0_46)
    | ~ m1_pre_topc(X0_46,sK0)
    | ~ m1_pre_topc(X1_46,sK0)
    | ~ m1_pre_topc(X2_46,sK0)
    | v2_struct_0(X0_46)
    | v2_struct_0(X1_46)
    | v2_struct_0(X2_46) ),
    inference(subtyping,[status(esa)],[c_583])).

cnf(c_1669,plain,
    ( r1_tsep_1(X0_46,X1_46) != iProver_top
    | r1_tsep_1(X1_46,X2_46) = iProver_top
    | m1_pre_topc(X2_46,X0_46) != iProver_top
    | m1_pre_topc(X0_46,sK0) != iProver_top
    | m1_pre_topc(X1_46,sK0) != iProver_top
    | m1_pre_topc(X2_46,sK0) != iProver_top
    | v2_struct_0(X2_46) = iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v2_struct_0(X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1083])).

cnf(c_5857,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,sK2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | r1_tsep_1(sK2,X0_46) = iProver_top
    | m1_pre_topc(X0_46,sK3) != iProver_top
    | m1_pre_topc(X0_46,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5849,c_1669])).

cnf(c_39,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_41,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_18215,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,sK2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | r1_tsep_1(sK2,X0_46) = iProver_top
    | m1_pre_topc(X0_46,sK3) != iProver_top
    | m1_pre_topc(X0_46,sK0) != iProver_top
    | v2_struct_0(X0_46) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5857,c_38,c_39,c_40,c_41])).

cnf(c_18227,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,sK2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | r1_tsep_1(sK2,sK2) = iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1661,c_18215])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_36,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_42,plain,
    ( r1_tsep_1(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK2,sK3)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_43,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1101,plain,
    ( ~ m1_pre_topc(X0_46,X1_46)
    | ~ l1_pre_topc(X1_46)
    | l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1651,plain,
    ( m1_pre_topc(X0_46,X1_46) != iProver_top
    | l1_pre_topc(X1_46) != iProver_top
    | l1_pre_topc(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1101])).

cnf(c_3987,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1661,c_1651])).

cnf(c_4196,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3987,c_35])).

cnf(c_6,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1102,plain,
    ( l1_struct_0(X0_46)
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1650,plain,
    ( l1_struct_0(X0_46) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1102])).

cnf(c_4201,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4196,c_1650])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1089,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1663,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1089])).

cnf(c_3988,plain,
    ( l1_pre_topc(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_1651])).

cnf(c_4204,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3988,c_35])).

cnf(c_4209,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4204,c_1650])).

cnf(c_8,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1100,plain,
    ( ~ r1_tsep_1(X0_46,X1_46)
    | r1_tsep_1(X1_46,X0_46)
    | ~ l1_struct_0(X1_46)
    | ~ l1_struct_0(X0_46) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_5103,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | r1_tsep_1(sK1,sK2)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1100])).

cnf(c_5104,plain,
    ( r1_tsep_1(sK2,sK1) != iProver_top
    | r1_tsep_1(sK1,sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5103])).

cnf(c_18228,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,sK2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | r1_tsep_1(sK2,sK1) = iProver_top
    | m1_pre_topc(sK1,sK3) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_18215])).

cnf(c_18458,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,sK2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | r1_tsep_1(sK2,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18227,c_36,c_38,c_42,c_43,c_4201,c_4209,c_5104,c_18228])).

cnf(c_13,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X2,X0)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_544,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | sK0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_31])).

cnf(c_545,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_544])).

cnf(c_547,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_545,c_32,c_30])).

cnf(c_548,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_547])).

cnf(c_1084,plain,
    ( ~ r1_tsep_1(X0_46,X1_46)
    | r1_tsep_1(X2_46,X1_46)
    | ~ m1_pre_topc(X2_46,X0_46)
    | ~ m1_pre_topc(X0_46,sK0)
    | ~ m1_pre_topc(X1_46,sK0)
    | ~ m1_pre_topc(X2_46,sK0)
    | v2_struct_0(X0_46)
    | v2_struct_0(X1_46)
    | v2_struct_0(X2_46) ),
    inference(subtyping,[status(esa)],[c_548])).

cnf(c_1668,plain,
    ( r1_tsep_1(X0_46,X1_46) != iProver_top
    | r1_tsep_1(X2_46,X1_46) = iProver_top
    | m1_pre_topc(X2_46,X0_46) != iProver_top
    | m1_pre_topc(X0_46,sK0) != iProver_top
    | m1_pre_topc(X1_46,sK0) != iProver_top
    | m1_pre_topc(X2_46,sK0) != iProver_top
    | v2_struct_0(X2_46) = iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v2_struct_0(X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1084])).

cnf(c_18468,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,sK2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | r1_tsep_1(X0_46,sK2) = iProver_top
    | m1_pre_topc(X0_46,sK2) != iProver_top
    | m1_pre_topc(X0_46,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_18458,c_1668])).

cnf(c_37,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_20,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_45,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) != iProver_top
    | m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2343,plain,
    ( ~ m1_pre_topc(sK3,X0_46)
    | ~ l1_pre_topc(X0_46)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1101])).

cnf(c_2344,plain,
    ( m1_pre_topc(sK3,X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2343])).

cnf(c_2346,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2344])).

cnf(c_2149,plain,
    ( ~ m1_pre_topc(X0_46,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0_46,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0_46)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1105])).

cnf(c_2437,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2149])).

cnf(c_2438,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2437])).

cnf(c_2154,plain,
    ( ~ m1_pre_topc(X0_46,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0_46,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0_46)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1105])).

cnf(c_2449,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2154])).

cnf(c_2450,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2449])).

cnf(c_9,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_16,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_224,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_405,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | k1_zfmisc_1(u1_struct_0(X3)) != k1_zfmisc_1(X1)
    | u1_struct_0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_224])).

cnf(c_406,plain,
    ( r1_tarski(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ l1_pre_topc(X2)
    | k1_zfmisc_1(u1_struct_0(X2)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_1085,plain,
    ( r1_tarski(u1_struct_0(X0_46),X0_45)
    | ~ m1_pre_topc(X0_46,X1_46)
    | ~ l1_pre_topc(X1_46)
    | k1_zfmisc_1(u1_struct_0(X1_46)) != k1_zfmisc_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_406])).

cnf(c_2060,plain,
    ( r1_tarski(u1_struct_0(sK2),X0_45)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(X0_45) ),
    inference(instantiation,[status(thm)],[c_1085])).

cnf(c_3973,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2060])).

cnf(c_3975,plain,
    ( k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3973])).

cnf(c_1112,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_3974,plain,
    ( k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1112])).

cnf(c_18,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_684,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_31])).

cnf(c_685,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_684])).

cnf(c_687,plain,
    ( ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(X0,X1)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_685,c_30])).

cnf(c_688,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0) ),
    inference(renaming,[status(thm)],[c_687])).

cnf(c_1080,plain,
    ( ~ r1_tarski(u1_struct_0(X0_46),u1_struct_0(X1_46))
    | m1_pre_topc(X0_46,X1_46)
    | ~ m1_pre_topc(X0_46,sK0)
    | ~ m1_pre_topc(X1_46,sK0) ),
    inference(subtyping,[status(esa)],[c_688])).

cnf(c_3393,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0_46))
    | ~ m1_pre_topc(X0_46,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0_46)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    inference(instantiation,[status(thm)],[c_1080])).

cnf(c_11421,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK1,sK3)))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    inference(instantiation,[status(thm)],[c_3393])).

cnf(c_11422,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK1,sK3))) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) = iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11421])).

cnf(c_1095,negated_conjecture,
    ( m1_pre_topc(sK2,sK3)
    | m1_pre_topc(sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1657,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1095])).

cnf(c_5144,plain,
    ( u1_struct_0(k2_tsep_1(sK0,X0_46,sK3)) = k3_xboole_0(u1_struct_0(X0_46),u1_struct_0(sK3))
    | r1_tsep_1(X0_46,sK3) = iProver_top
    | m1_pre_topc(X0_46,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1659,c_1905])).

cnf(c_5275,plain,
    ( m1_pre_topc(X0_46,sK0) != iProver_top
    | r1_tsep_1(X0_46,sK3) = iProver_top
    | u1_struct_0(k2_tsep_1(sK0,X0_46,sK3)) = k3_xboole_0(u1_struct_0(X0_46),u1_struct_0(sK3))
    | v2_struct_0(X0_46) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5144,c_33,c_35,c_40])).

cnf(c_5276,plain,
    ( u1_struct_0(k2_tsep_1(sK0,X0_46,sK3)) = k3_xboole_0(u1_struct_0(X0_46),u1_struct_0(sK3))
    | r1_tsep_1(X0_46,sK3) = iProver_top
    | m1_pre_topc(X0_46,sK0) != iProver_top
    | v2_struct_0(X0_46) = iProver_top ),
    inference(renaming,[status(thm)],[c_5275])).

cnf(c_5287,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK3)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | r1_tsep_1(sK1,sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_5276])).

cnf(c_5602,plain,
    ( r1_tsep_1(sK1,sK3) = iProver_top
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK3)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5287,c_36])).

cnf(c_5603,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK3)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | r1_tsep_1(sK1,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_5602])).

cnf(c_10,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_649,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | sK0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_31])).

cnf(c_650,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_649])).

cnf(c_652,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_650,c_32,c_30])).

cnf(c_653,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_652])).

cnf(c_1081,plain,
    ( ~ r1_tsep_1(X0_46,X1_46)
    | r1_tsep_1(X0_46,X2_46)
    | ~ m1_pre_topc(X2_46,X1_46)
    | ~ m1_pre_topc(X0_46,sK0)
    | ~ m1_pre_topc(X1_46,sK0)
    | ~ m1_pre_topc(X2_46,sK0)
    | v2_struct_0(X0_46)
    | v2_struct_0(X1_46)
    | v2_struct_0(X2_46) ),
    inference(subtyping,[status(esa)],[c_653])).

cnf(c_1671,plain,
    ( r1_tsep_1(X0_46,X1_46) != iProver_top
    | r1_tsep_1(X0_46,X2_46) = iProver_top
    | m1_pre_topc(X2_46,X1_46) != iProver_top
    | m1_pre_topc(X0_46,sK0) != iProver_top
    | m1_pre_topc(X1_46,sK0) != iProver_top
    | m1_pre_topc(X2_46,sK0) != iProver_top
    | v2_struct_0(X2_46) = iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v2_struct_0(X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1081])).

cnf(c_5609,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK3)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | r1_tsep_1(sK1,X0_46) = iProver_top
    | m1_pre_topc(X0_46,sK3) != iProver_top
    | m1_pre_topc(X0_46,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5603,c_1671])).

cnf(c_13432,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK3)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | r1_tsep_1(sK1,X0_46) = iProver_top
    | m1_pre_topc(X0_46,sK3) != iProver_top
    | m1_pre_topc(X0_46,sK0) != iProver_top
    | v2_struct_0(X0_46) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5609,c_36,c_37,c_40,c_41])).

cnf(c_13444,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK3)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | r1_tsep_1(sK1,sK2) = iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1661,c_13432])).

cnf(c_13489,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK3)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13444,c_38,c_42])).

cnf(c_13490,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK3)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | m1_pre_topc(sK2,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_13489])).

cnf(c_13495,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK3)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1657,c_13490])).

cnf(c_18504,plain,
    ( m1_pre_topc(sK1,sK3) != iProver_top
    | u1_struct_0(k2_tsep_1(sK0,sK3,sK2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18228,c_36,c_42,c_4201,c_4209,c_5104])).

cnf(c_18505,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,sK2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | m1_pre_topc(sK1,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_18504])).

cnf(c_18510,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,sK2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK3)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_13495,c_18505])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1108,plain,
    ( k3_xboole_0(X0_45,X1_45) = k3_xboole_0(X1_45,X0_45) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_18568,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,sK2)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK3)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_18510,c_1108])).

cnf(c_21,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
    | m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_44,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) != iProver_top
    | m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2443,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2154])).

cnf(c_2444,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2443])).

cnf(c_11424,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK2)))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    inference(instantiation,[status(thm)],[c_3393])).

cnf(c_11425,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK2))) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) = iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11424])).

cnf(c_2323,plain,
    ( r1_tarski(u1_struct_0(sK1),X0_45)
    | ~ m1_pre_topc(sK1,X0_46)
    | ~ l1_pre_topc(X0_46)
    | k1_zfmisc_1(u1_struct_0(X0_46)) != k1_zfmisc_1(X0_45) ),
    inference(instantiation,[status(thm)],[c_1085])).

cnf(c_13536,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK1,sK3)
    | ~ l1_pre_topc(sK3)
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2323])).

cnf(c_13537,plain,
    ( k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(sK1,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13536])).

cnf(c_5803,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | r1_tsep_1(sK1,sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_5792])).

cnf(c_2110,plain,
    ( ~ m1_pre_topc(X0_46,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0_46)
    | ~ v2_struct_0(k2_tsep_1(sK0,X0_46,sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1103])).

cnf(c_2373,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2110])).

cnf(c_2134,plain,
    ( ~ m1_pre_topc(X0_46,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0_46)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | v1_pre_topc(k2_tsep_1(sK0,X0_46,sK2)) ),
    inference(instantiation,[status(thm)],[c_1104])).

cnf(c_2411,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2134])).

cnf(c_2179,plain,
    ( r1_tsep_1(sK1,X0_46)
    | ~ m1_pre_topc(X0_46,sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X0_46),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0_46)
    | v2_struct_0(k2_tsep_1(sK0,sK1,X0_46))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,X0_46))
    | u1_struct_0(k2_tsep_1(sK0,sK1,X0_46)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_46)) ),
    inference(instantiation,[status(thm)],[c_1106])).

cnf(c_2520,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2179])).

cnf(c_6008,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5803,c_32,c_30,c_29,c_28,c_27,c_26,c_23,c_2373,c_2411,c_2449,c_2520])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1099,plain,
    ( ~ r1_tarski(X0_45,X1_45)
    | r1_tarski(k3_xboole_0(X0_45,X2_45),k3_xboole_0(X1_45,X2_45)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1653,plain,
    ( r1_tarski(X0_45,X1_45) != iProver_top
    | r1_tarski(k3_xboole_0(X0_45,X2_45),k3_xboole_0(X1_45,X2_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1099])).

cnf(c_6012,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k3_xboole_0(X0_45,u1_struct_0(sK2))) = iProver_top
    | r1_tarski(u1_struct_0(sK1),X0_45) != iProver_top ),
    inference(superposition,[status(thm)],[c_6008,c_1653])).

cnf(c_18578,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK3)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK2))) = iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18510,c_6012])).

cnf(c_18852,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK3)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18568,c_33,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_44,c_2346,c_2444,c_2450,c_3974,c_11425,c_13490,c_13495,c_13537,c_18578])).

cnf(c_2724,plain,
    ( r1_tarski(X0_45,X1_45) != iProver_top
    | r1_tarski(k3_xboole_0(X2_45,X0_45),k3_xboole_0(X1_45,X2_45)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1108,c_1653])).

cnf(c_2743,plain,
    ( r1_tarski(X0_45,X1_45) != iProver_top
    | r1_tarski(k3_xboole_0(X2_45,X0_45),k3_xboole_0(X2_45,X1_45)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1108,c_2724])).

cnf(c_6017,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k3_xboole_0(u1_struct_0(sK1),X0_45)) = iProver_top
    | r1_tarski(u1_struct_0(sK2),X0_45) != iProver_top ),
    inference(superposition,[status(thm)],[c_6008,c_2743])).

cnf(c_18866,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK1,sK3))) = iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18852,c_6017])).

cnf(c_19143,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,sK2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18468,c_33,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_45,c_2346,c_2438,c_2450,c_3975,c_3974,c_4201,c_4209,c_5104,c_11422,c_18228,c_18866])).

cnf(c_19163,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK2))) = iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19143,c_6012])).

cnf(c_19,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_46,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19163,c_18866,c_13537,c_11425,c_11422,c_3974,c_3975,c_2450,c_2444,c_2438,c_2346,c_46,c_45,c_44,c_43,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_33])).


%------------------------------------------------------------------------------
