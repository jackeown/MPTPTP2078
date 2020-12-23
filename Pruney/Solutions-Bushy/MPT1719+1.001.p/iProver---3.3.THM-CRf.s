%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1719+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:16 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  205 (1507 expanded)
%              Number of clauses        :  140 ( 403 expanded)
%              Number of leaves         :   15 ( 541 expanded)
%              Depth                    :   25
%              Number of atoms          :  836 (16966 expanded)
%              Number of equality atoms :  193 ( 483 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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
                     => ( ( m1_pre_topc(X2,X4)
                          & m1_pre_topc(X1,X3) )
                       => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                          | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
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
                       => ( ( m1_pre_topc(X2,X4)
                            & m1_pre_topc(X1,X3) )
                         => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                            | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      & ~ r1_tsep_1(X1,X2)
                      & m1_pre_topc(X2,X4)
                      & m1_pre_topc(X1,X3)
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
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      & ~ r1_tsep_1(X1,X2)
                      & m1_pre_topc(X2,X4)
                      & m1_pre_topc(X1,X3)
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
    inference(flattening,[],[f24])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
          & ~ r1_tsep_1(X1,X2)
          & m1_pre_topc(X2,X4)
          & m1_pre_topc(X1,X3)
          & m1_pre_topc(X4,X0)
          & ~ v2_struct_0(X4) )
     => ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,sK4))
        & ~ r1_tsep_1(X1,X2)
        & m1_pre_topc(X2,sK4)
        & m1_pre_topc(X1,X3)
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X4)
              & m1_pre_topc(X1,X3)
              & m1_pre_topc(X4,X0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,sK3,X4))
            & ~ r1_tsep_1(X1,X2)
            & m1_pre_topc(X2,X4)
            & m1_pre_topc(X1,sK3)
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
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X4)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X4,X0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ m1_pre_topc(k2_tsep_1(X0,X1,sK2),k2_tsep_1(X0,X3,X4))
                & ~ r1_tsep_1(X1,sK2)
                & m1_pre_topc(sK2,X4)
                & m1_pre_topc(X1,X3)
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
                      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      & ~ r1_tsep_1(X1,X2)
                      & m1_pre_topc(X2,X4)
                      & m1_pre_topc(X1,X3)
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
                    ( ~ m1_pre_topc(k2_tsep_1(X0,sK1,X2),k2_tsep_1(X0,X3,X4))
                    & ~ r1_tsep_1(sK1,X2)
                    & m1_pre_topc(X2,X4)
                    & m1_pre_topc(sK1,X3)
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
                        ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                        & ~ r1_tsep_1(X1,X2)
                        & m1_pre_topc(X2,X4)
                        & m1_pre_topc(X1,X3)
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
                      ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X3,X4))
                      & ~ r1_tsep_1(X1,X2)
                      & m1_pre_topc(X2,X4)
                      & m1_pre_topc(X1,X3)
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
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4))
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK2,sK4)
    & m1_pre_topc(sK1,sK3)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f25,f34,f33,f32,f31,f30])).

fof(f59,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f35])).

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
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
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

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
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
    inference(flattening,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
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
    inference(nnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
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
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
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
    inference(equality_resolution,[],[f38])).

fof(f4,axiom,(
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
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

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
    inference(flattening,[],[f15])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    m1_pre_topc(sK2,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4)) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
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

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f64,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1157,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1665,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1157])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1159,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1663,plain,
    ( m1_pre_topc(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1159])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
    | r1_tsep_1(X2,X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(X1,X2,X0))
    | ~ v1_pre_topc(k2_tsep_1(X1,X2,X0))
    | u1_struct_0(k2_tsep_1(X1,X2,X0)) = k3_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v1_pre_topc(k2_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_173,plain,
    ( ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | r1_tsep_1(X2,X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | u1_struct_0(k2_tsep_1(X1,X2,X0)) = k3_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_8,c_7,c_6])).

cnf(c_174,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | r1_tsep_1(X2,X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | u1_struct_0(k2_tsep_1(X1,X2,X0)) = k3_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(renaming,[status(thm)],[c_173])).

cnf(c_1149,plain,
    ( ~ m1_pre_topc(X0_46,X1_46)
    | ~ m1_pre_topc(X2_46,X1_46)
    | r1_tsep_1(X2_46,X0_46)
    | ~ l1_pre_topc(X1_46)
    | v2_struct_0(X0_46)
    | v2_struct_0(X1_46)
    | v2_struct_0(X2_46)
    | u1_struct_0(k2_tsep_1(X1_46,X2_46,X0_46)) = k3_xboole_0(u1_struct_0(X2_46),u1_struct_0(X0_46)) ),
    inference(subtyping,[status(esa)],[c_174])).

cnf(c_1673,plain,
    ( u1_struct_0(k2_tsep_1(X0_46,X1_46,X2_46)) = k3_xboole_0(u1_struct_0(X1_46),u1_struct_0(X2_46))
    | m1_pre_topc(X2_46,X0_46) != iProver_top
    | m1_pre_topc(X1_46,X0_46) != iProver_top
    | r1_tsep_1(X1_46,X2_46) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v2_struct_0(X1_46) = iProver_top
    | v2_struct_0(X2_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1149])).

cnf(c_3751,plain,
    ( k3_xboole_0(u1_struct_0(X0_46),u1_struct_0(sK4)) = u1_struct_0(k2_tsep_1(sK0,X0_46,sK4))
    | m1_pre_topc(X0_46,sK0) != iProver_top
    | r1_tsep_1(X0_46,sK4) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_1673])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_30,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_32,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_39,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4829,plain,
    ( r1_tsep_1(X0_46,sK4) = iProver_top
    | m1_pre_topc(X0_46,sK0) != iProver_top
    | k3_xboole_0(u1_struct_0(X0_46),u1_struct_0(sK4)) = u1_struct_0(k2_tsep_1(sK0,X0_46,sK4))
    | v2_struct_0(X0_46) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3751,c_30,c_32,c_39])).

cnf(c_4830,plain,
    ( k3_xboole_0(u1_struct_0(X0_46),u1_struct_0(sK4)) = u1_struct_0(k2_tsep_1(sK0,X0_46,sK4))
    | m1_pre_topc(X0_46,sK0) != iProver_top
    | r1_tsep_1(X0_46,sK4) = iProver_top
    | v2_struct_0(X0_46) = iProver_top ),
    inference(renaming,[status(thm)],[c_4829])).

cnf(c_4836,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k2_tsep_1(sK0,sK3,sK4))
    | r1_tsep_1(sK3,sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1665,c_4830])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_37,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4922,plain,
    ( r1_tsep_1(sK3,sK4) = iProver_top
    | k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k2_tsep_1(sK0,sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4836,c_37])).

cnf(c_4923,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k2_tsep_1(sK0,sK3,sK4))
    | r1_tsep_1(sK3,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_4922])).

cnf(c_1,plain,
    ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tsep_1(X0,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_218,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_439,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | k3_xboole_0(X2,X3) = k1_xboole_0
    | u1_struct_0(X0) != X2
    | u1_struct_0(X1) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_218])).

cnf(c_440,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_1146,plain,
    ( ~ r1_tsep_1(X0_46,X1_46)
    | ~ l1_struct_0(X1_46)
    | ~ l1_struct_0(X0_46)
    | k3_xboole_0(u1_struct_0(X0_46),u1_struct_0(X1_46)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_440])).

cnf(c_1676,plain,
    ( k3_xboole_0(u1_struct_0(X0_46),u1_struct_0(X1_46)) = k1_xboole_0
    | r1_tsep_1(X0_46,X1_46) != iProver_top
    | l1_struct_0(X0_46) != iProver_top
    | l1_struct_0(X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1146])).

cnf(c_4956,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k2_tsep_1(sK0,sK3,sK4))
    | k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = k1_xboole_0
    | l1_struct_0(sK4) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4923,c_1676])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1166,plain,
    ( ~ m1_pre_topc(X0_46,X1_46)
    | ~ l1_pre_topc(X1_46)
    | l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1656,plain,
    ( m1_pre_topc(X0_46,X1_46) != iProver_top
    | l1_pre_topc(X1_46) != iProver_top
    | l1_pre_topc(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1166])).

cnf(c_2759,plain,
    ( l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_1656])).

cnf(c_40,plain,
    ( m1_pre_topc(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2004,plain,
    ( ~ m1_pre_topc(sK4,X0_46)
    | ~ l1_pre_topc(X0_46)
    | l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1166])).

cnf(c_2005,plain,
    ( m1_pre_topc(sK4,X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top
    | l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2004])).

cnf(c_2007,plain,
    ( m1_pre_topc(sK4,sK0) != iProver_top
    | l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2005])).

cnf(c_3190,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2759,c_32,c_40,c_2007])).

cnf(c_9,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1167,plain,
    ( ~ l1_pre_topc(X0_46)
    | l1_struct_0(X0_46) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1655,plain,
    ( l1_pre_topc(X0_46) != iProver_top
    | l1_struct_0(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1167])).

cnf(c_3194,plain,
    ( l1_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3190,c_1655])).

cnf(c_2760,plain,
    ( l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1665,c_1656])).

cnf(c_38,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2014,plain,
    ( ~ m1_pre_topc(sK3,X0_46)
    | ~ l1_pre_topc(X0_46)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1166])).

cnf(c_2015,plain,
    ( m1_pre_topc(sK3,X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2014])).

cnf(c_2017,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2015])).

cnf(c_3221,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2760,c_32,c_38,c_2017])).

cnf(c_3225,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3221,c_1655])).

cnf(c_5891,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k2_tsep_1(sK0,sK3,sK4))
    | k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4956,c_3194,c_3225])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k3_xboole_0(X2,X0),k3_xboole_0(X3,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1165,plain,
    ( ~ r1_tarski(X0_47,X1_47)
    | ~ r1_tarski(X2_47,X3_47)
    | r1_tarski(k3_xboole_0(X2_47,X0_47),k3_xboole_0(X3_47,X1_47)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1657,plain,
    ( r1_tarski(X0_47,X1_47) != iProver_top
    | r1_tarski(X2_47,X3_47) != iProver_top
    | r1_tarski(k3_xboole_0(X2_47,X0_47),k3_xboole_0(X3_47,X1_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1165])).

cnf(c_5895,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = k1_xboole_0
    | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK3,sK4)),k3_xboole_0(X0_47,X1_47)) = iProver_top
    | r1_tarski(u1_struct_0(sK4),X1_47) != iProver_top
    | r1_tarski(u1_struct_0(sK3),X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_5891,c_1657])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK2,sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_15,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_13,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_403,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ l1_pre_topc(X2)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_28])).

cnf(c_404,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_408,plain,
    ( ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_404,c_27])).

cnf(c_409,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0) ),
    inference(renaming,[status(thm)],[c_408])).

cnf(c_1147,plain,
    ( r1_tarski(u1_struct_0(X0_46),u1_struct_0(X1_46))
    | ~ m1_pre_topc(X0_46,X1_46)
    | ~ m1_pre_topc(X0_46,sK0)
    | ~ m1_pre_topc(X1_46,sK0) ),
    inference(subtyping,[status(esa)],[c_409])).

cnf(c_1906,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_46))
    | ~ m1_pre_topc(X0_46,sK0)
    | ~ m1_pre_topc(sK2,X0_46)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_1147])).

cnf(c_2075,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK2,sK4)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_1906])).

cnf(c_1911,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(X0_46))
    | ~ m1_pre_topc(X0_46,sK0)
    | ~ m1_pre_topc(sK1,X0_46)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_1147])).

cnf(c_2090,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_1911])).

cnf(c_1170,plain,
    ( ~ m1_pre_topc(X0_46,X1_46)
    | ~ m1_pre_topc(X2_46,X1_46)
    | m1_pre_topc(k2_tsep_1(X1_46,X2_46,X0_46),X1_46)
    | ~ l1_pre_topc(X1_46)
    | v2_struct_0(X0_46)
    | v2_struct_0(X1_46)
    | v2_struct_0(X2_46) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1770,plain,
    ( ~ m1_pre_topc(X0_46,X1_46)
    | m1_pre_topc(k2_tsep_1(X1_46,X0_46,sK2),X1_46)
    | ~ m1_pre_topc(sK2,X1_46)
    | ~ l1_pre_topc(X1_46)
    | v2_struct_0(X1_46)
    | v2_struct_0(X0_46)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1170])).

cnf(c_2606,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1770])).

cnf(c_1844,plain,
    ( ~ m1_pre_topc(X0_46,X1_46)
    | m1_pre_topc(k2_tsep_1(X1_46,X0_46,sK4),X1_46)
    | ~ m1_pre_topc(sK4,X1_46)
    | ~ l1_pre_topc(X1_46)
    | v2_struct_0(X1_46)
    | v2_struct_0(X0_46)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1170])).

cnf(c_2660,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1844])).

cnf(c_1153,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1669,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1153])).

cnf(c_1155,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1667,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1155])).

cnf(c_3753,plain,
    ( k3_xboole_0(u1_struct_0(X0_46),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,X0_46,sK2))
    | m1_pre_topc(X0_46,sK0) != iProver_top
    | r1_tsep_1(X0_46,sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1667,c_1673])).

cnf(c_35,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5170,plain,
    ( r1_tsep_1(X0_46,sK2) = iProver_top
    | m1_pre_topc(X0_46,sK0) != iProver_top
    | k3_xboole_0(u1_struct_0(X0_46),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,X0_46,sK2))
    | v2_struct_0(X0_46) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3753,c_30,c_32,c_35])).

cnf(c_5171,plain,
    ( k3_xboole_0(u1_struct_0(X0_46),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,X0_46,sK2))
    | m1_pre_topc(X0_46,sK0) != iProver_top
    | r1_tsep_1(X0_46,sK2) = iProver_top
    | v2_struct_0(X0_46) = iProver_top ),
    inference(renaming,[status(thm)],[c_5170])).

cnf(c_5179,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK1,sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1669,c_5171])).

cnf(c_33,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_43,plain,
    ( r1_tsep_1(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5236,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5179,c_33,c_43])).

cnf(c_5239,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k3_xboole_0(X0_47,X1_47)) = iProver_top
    | r1_tarski(u1_struct_0(sK2),X1_47) != iProver_top
    | r1_tarski(u1_struct_0(sK1),X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_5236,c_1657])).

cnf(c_5900,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = k1_xboole_0
    | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4))) = iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4)) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5891,c_5239])).

cnf(c_5916,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4)))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3))
    | k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5900])).

cnf(c_14,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_383,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_28])).

cnf(c_384,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_386,plain,
    ( ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(X0,X1)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_384,c_27])).

cnf(c_387,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0) ),
    inference(renaming,[status(thm)],[c_386])).

cnf(c_1148,plain,
    ( ~ r1_tarski(u1_struct_0(X0_46),u1_struct_0(X1_46))
    | m1_pre_topc(X0_46,X1_46)
    | ~ m1_pre_topc(X0_46,sK0)
    | ~ m1_pre_topc(X1_46,sK0) ),
    inference(subtyping,[status(esa)],[c_387])).

cnf(c_4118,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0_46))
    | ~ m1_pre_topc(X0_46,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0_46)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    inference(instantiation,[status(thm)],[c_1148])).

cnf(c_8122,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4)))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    inference(instantiation,[status(thm)],[c_4118])).

cnf(c_8151,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5895,c_29,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_18,c_17,c_15,c_2075,c_2090,c_2606,c_2660,c_5916,c_8122])).

cnf(c_8169,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k1_xboole_0) = iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4)) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8151,c_5239])).

cnf(c_34,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_36,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_41,plain,
    ( m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_42,plain,
    ( m1_pre_topc(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2076,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4)) = iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_pre_topc(sK2,sK4) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2075])).

cnf(c_2091,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK3) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2090])).

cnf(c_8316,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8169,c_34,c_36,c_38,c_40,c_41,c_42,c_2076,c_2091])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1164,plain,
    ( ~ r1_tarski(X0_47,k1_xboole_0)
    | k1_xboole_0 = X0_47 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1658,plain,
    ( k1_xboole_0 = X0_47
    | r1_tarski(X0_47,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1164])).

cnf(c_8320,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8316,c_1658])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | r1_tsep_1(X0,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_216,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_457,plain,
    ( r1_tsep_1(X0,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | k3_xboole_0(X2,X3) != k1_xboole_0
    | u1_struct_0(X0) != X2
    | u1_struct_0(X1) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_216])).

cnf(c_458,plain,
    ( r1_tsep_1(X0,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_1145,plain,
    ( r1_tsep_1(X0_46,X1_46)
    | ~ l1_struct_0(X1_46)
    | ~ l1_struct_0(X0_46)
    | k3_xboole_0(u1_struct_0(X0_46),u1_struct_0(X1_46)) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_458])).

cnf(c_1677,plain,
    ( k3_xboole_0(u1_struct_0(X0_46),u1_struct_0(X1_46)) != k1_xboole_0
    | r1_tsep_1(X0_46,X1_46) = iProver_top
    | l1_struct_0(X0_46) != iProver_top
    | l1_struct_0(X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1145])).

cnf(c_5320,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) != k1_xboole_0
    | r1_tsep_1(sK1,sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5236,c_1677])).

cnf(c_1160,negated_conjecture,
    ( m1_pre_topc(sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1662,plain,
    ( m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1160])).

cnf(c_2758,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1662,c_1656])).

cnf(c_3183,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2758,c_32,c_38,c_2017])).

cnf(c_3187,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3183,c_1655])).

cnf(c_1161,negated_conjecture,
    ( m1_pre_topc(sK2,sK4) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1661,plain,
    ( m1_pre_topc(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1161])).

cnf(c_2757,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1661,c_1656])).

cnf(c_1996,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1167])).

cnf(c_1997,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1996])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8320,c_5320,c_3187,c_2757,c_2007,c_1997,c_43,c_40,c_32])).


%------------------------------------------------------------------------------
