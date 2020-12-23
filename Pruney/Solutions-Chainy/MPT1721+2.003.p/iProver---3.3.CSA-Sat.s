%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:11 EST 2020

% Result     : CounterSatisfiable 2.09s
% Output     : Saturation 2.09s
% Verified   : 
% Statistics : Number of formulae       :  178 (4262 expanded)
%              Number of clauses        :  133 (1097 expanded)
%              Number of leaves         :   16 (1447 expanded)
%              Depth                    :   22
%              Number of atoms          :  867 (46772 expanded)
%              Number of equality atoms :  319 (1959 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   26 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
                 => ( ( m1_pre_topc(X2,X3)
                      & m1_pre_topc(X1,X3) )
                   => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                      | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
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
                   => ( ( m1_pre_topc(X2,X3)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                        | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
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

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
          & ~ r1_tsep_1(X1,X2)
          & m1_pre_topc(X2,X3)
          & m1_pre_topc(X1,X3)
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),sK3)
        & ~ r1_tsep_1(X1,X2)
        & m1_pre_topc(X2,sK3)
        & m1_pre_topc(X1,sK3)
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X3)
              & m1_pre_topc(X1,X3)
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ m1_pre_topc(k2_tsep_1(X0,X1,sK2),X3)
            & ~ r1_tsep_1(X1,sK2)
            & m1_pre_topc(sK2,X3)
            & m1_pre_topc(X1,X3)
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k2_tsep_1(X0,sK1,X2),X3)
                & ~ r1_tsep_1(sK1,X2)
                & m1_pre_topc(X2,X3)
                & m1_pre_topc(sK1,X3)
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X1,X3)
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
                  ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
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

fof(f27,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK2,sK3)
    & m1_pre_topc(sK1,sK3)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f26,f25,f24,f23])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

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
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

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
    inference(flattening,[],[f12])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f30,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
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
    inference(equality_resolution,[],[f30])).

fof(f49,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f14,plain,(
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
    inference(flattening,[],[f14])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tsep_1(X0,X1,X2) = X3
      | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
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
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_211,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_210,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_202,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_879,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_7,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_874,plain,
    ( m1_pre_topc(X0_42,X0_42)
    | ~ l1_pre_topc(X0_42) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1215,plain,
    ( m1_pre_topc(X0_42,X0_42) = iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_874])).

cnf(c_12,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_872,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1217,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_872])).

cnf(c_3,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(k2_tsep_1(X2,X0,X1),X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k2_tsep_1(X2,X0,X1))
    | ~ v1_pre_topc(k2_tsep_1(X2,X0,X1))
    | ~ l1_pre_topc(X2)
    | u1_struct_0(k2_tsep_1(X2,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_236,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k2_tsep_1(X1,X0,X2))
    | ~ v1_pre_topc(k2_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k2_tsep_1(X1,X0,X2)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X2))
    | sK2 != X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_11])).

cnf(c_237,plain,
    ( ~ m1_pre_topc(k2_tsep_1(X0,sK1,sK2),X0)
    | ~ m1_pre_topc(sK2,X0)
    | ~ m1_pre_topc(sK1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(X0,sK1,sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ v1_pre_topc(k2_tsep_1(X0,sK1,sK2))
    | ~ l1_pre_topc(X0)
    | u1_struct_0(k2_tsep_1(X0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_241,plain,
    ( ~ m1_pre_topc(k2_tsep_1(X0,sK1,sK2),X0)
    | ~ m1_pre_topc(sK2,X0)
    | ~ m1_pre_topc(sK1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(X0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(X0,sK1,sK2))
    | ~ l1_pre_topc(X0)
    | u1_struct_0(k2_tsep_1(X0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_237,c_19,c_17])).

cnf(c_862,plain,
    ( ~ m1_pre_topc(k2_tsep_1(X0_42,sK1,sK2),X0_42)
    | ~ m1_pre_topc(sK2,X0_42)
    | ~ m1_pre_topc(sK1,X0_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(k2_tsep_1(X0_42,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(X0_42,sK1,sK2))
    | ~ l1_pre_topc(X0_42)
    | u1_struct_0(k2_tsep_1(X0_42,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_241])).

cnf(c_1227,plain,
    ( u1_struct_0(k2_tsep_1(X0_42,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | m1_pre_topc(k2_tsep_1(X0_42,sK1,sK2),X0_42) != iProver_top
    | m1_pre_topc(sK2,X0_42) != iProver_top
    | m1_pre_topc(sK1,X0_42) != iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v2_struct_0(k2_tsep_1(X0_42,sK1,sK2)) = iProver_top
    | v1_pre_topc(k2_tsep_1(X0_42,sK1,sK2)) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_862])).

cnf(c_26,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_28,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_917,plain,
    ( u1_struct_0(k2_tsep_1(X0_42,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | m1_pre_topc(k2_tsep_1(X0_42,sK1,sK2),X0_42) != iProver_top
    | m1_pre_topc(sK2,X0_42) != iProver_top
    | m1_pre_topc(sK1,X0_42) != iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v2_struct_0(k2_tsep_1(X0_42,sK1,sK2)) = iProver_top
    | v1_pre_topc(k2_tsep_1(X0_42,sK1,sK2)) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_862])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v1_pre_topc(k2_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_876,plain,
    ( ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(X2_42,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X2_42)
    | v1_pre_topc(k2_tsep_1(X1_42,X0_42,X2_42))
    | ~ l1_pre_topc(X1_42) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1391,plain,
    ( ~ m1_pre_topc(sK2,X0_42)
    | ~ m1_pre_topc(sK1,X0_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v1_pre_topc(k2_tsep_1(X0_42,sK1,sK2))
    | ~ l1_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(c_1392,plain,
    ( m1_pre_topc(sK2,X0_42) != iProver_top
    | m1_pre_topc(sK1,X0_42) != iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_pre_topc(k2_tsep_1(X0_42,sK1,sK2)) = iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1391])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_877,plain,
    ( ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(X2_42,X1_42)
    | m1_pre_topc(k2_tsep_1(X1_42,X0_42,X2_42),X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X2_42)
    | ~ l1_pre_topc(X1_42) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1425,plain,
    ( m1_pre_topc(k2_tsep_1(X0_42,sK1,sK2),X0_42)
    | ~ m1_pre_topc(sK2,X0_42)
    | ~ m1_pre_topc(sK1,X0_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_877])).

cnf(c_1426,plain,
    ( m1_pre_topc(k2_tsep_1(X0_42,sK1,sK2),X0_42) = iProver_top
    | m1_pre_topc(sK2,X0_42) != iProver_top
    | m1_pre_topc(sK1,X0_42) != iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1425])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k2_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_875,plain,
    ( ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(X2_42,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X2_42)
    | ~ v2_struct_0(k2_tsep_1(X1_42,X0_42,X2_42))
    | ~ l1_pre_topc(X1_42) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1462,plain,
    ( ~ m1_pre_topc(sK2,X0_42)
    | ~ m1_pre_topc(sK1,X0_42)
    | v2_struct_0(X0_42)
    | ~ v2_struct_0(k2_tsep_1(X0_42,sK1,sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_875])).

cnf(c_1463,plain,
    ( m1_pre_topc(sK2,X0_42) != iProver_top
    | m1_pre_topc(sK1,X0_42) != iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v2_struct_0(k2_tsep_1(X0_42,sK1,sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1462])).

cnf(c_1808,plain,
    ( u1_struct_0(k2_tsep_1(X0_42,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | m1_pre_topc(sK2,X0_42) != iProver_top
    | m1_pre_topc(sK1,X0_42) != iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1227,c_26,c_28,c_917,c_1392,c_1426,c_1463])).

cnf(c_1819,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2))
    | m1_pre_topc(sK1,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1217,c_1808])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_25,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_15,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_30,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,negated_conjecture,
    ( m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_32,plain,
    ( m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_870,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1219,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_870])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_878,plain,
    ( ~ m1_pre_topc(X0_42,X1_42)
    | ~ l1_pre_topc(X1_42)
    | l1_pre_topc(X0_42) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1211,plain,
    ( m1_pre_topc(X0_42,X1_42) != iProver_top
    | l1_pre_topc(X1_42) != iProver_top
    | l1_pre_topc(X0_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_878])).

cnf(c_1510,plain,
    ( l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_1211])).

cnf(c_1953,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1819,c_25,c_30,c_32,c_1510])).

cnf(c_2,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | k2_tsep_1(X2,X0,X1) = X3
    | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) != u1_struct_0(X3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_272,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | k2_tsep_1(X1,X0,X3) = X2
    | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X3)) != u1_struct_0(X2)
    | sK2 != X3
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_273,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK2,X1)
    | ~ m1_pre_topc(sK1,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ v1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k2_tsep_1(X1,sK1,sK2) = X0
    | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_277,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK2,X1)
    | ~ m1_pre_topc(sK1,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k2_tsep_1(X1,sK1,sK2) = X0
    | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != u1_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_273,c_19,c_17])).

cnf(c_861,plain,
    ( ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(sK2,X1_42)
    | ~ m1_pre_topc(sK1,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | ~ v1_pre_topc(X0_42)
    | ~ l1_pre_topc(X1_42)
    | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != u1_struct_0(X0_42)
    | k2_tsep_1(X1_42,sK1,sK2) = X0_42 ),
    inference(subtyping,[status(esa)],[c_277])).

cnf(c_1228,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != u1_struct_0(X0_42)
    | k2_tsep_1(X1_42,sK1,sK2) = X0_42
    | m1_pre_topc(X0_42,X1_42) != iProver_top
    | m1_pre_topc(sK2,X1_42) != iProver_top
    | m1_pre_topc(sK1,X1_42) != iProver_top
    | v2_struct_0(X1_42) = iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v1_pre_topc(X0_42) != iProver_top
    | l1_pre_topc(X1_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_861])).

cnf(c_1957,plain,
    ( u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) != u1_struct_0(X0_42)
    | k2_tsep_1(X1_42,sK1,sK2) = X0_42
    | m1_pre_topc(X0_42,X1_42) != iProver_top
    | m1_pre_topc(sK2,X1_42) != iProver_top
    | m1_pre_topc(sK1,X1_42) != iProver_top
    | v2_struct_0(X1_42) = iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v1_pre_topc(X0_42) != iProver_top
    | l1_pre_topc(X1_42) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1953,c_1228])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_868,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1221,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_868])).

cnf(c_1820,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1221,c_1808])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_918,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_1393,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1391])).

cnf(c_1427,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1425])).

cnf(c_1464,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1462])).

cnf(c_881,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_1480,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_881])).

cnf(c_883,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_1435,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != X0_43
    | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0_42,X1_42,X2_42))
    | u1_struct_0(k2_tsep_1(X0_42,X1_42,X2_42)) != X0_43 ),
    inference(instantiation,[status(thm)],[c_883])).

cnf(c_1479,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0_42,X1_42,X2_42))
    | u1_struct_0(k2_tsep_1(X0_42,X1_42,X2_42)) != k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1435])).

cnf(c_1616,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0_42,sK1,sK2))
    | u1_struct_0(k2_tsep_1(X0_42,sK1,sK2)) != k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1479])).

cnf(c_1617,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) != k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1616])).

cnf(c_2234,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1820,c_22,c_20,c_19,c_18,c_17,c_16,c_918,c_1393,c_1427,c_1464,c_1480,c_1617])).

cnf(c_2237,plain,
    ( u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_2234,c_1953])).

cnf(c_2519,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) != u1_struct_0(X0_42)
    | k2_tsep_1(X1_42,sK1,sK2) = X0_42
    | m1_pre_topc(X0_42,X1_42) != iProver_top
    | m1_pre_topc(sK2,X1_42) != iProver_top
    | m1_pre_topc(sK1,X1_42) != iProver_top
    | v2_struct_0(X1_42) = iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v1_pre_topc(X0_42) != iProver_top
    | l1_pre_topc(X1_42) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1957,c_2237])).

cnf(c_2533,plain,
    ( k2_tsep_1(X0_42,sK1,sK2) = k2_tsep_1(sK0,sK1,sK2)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0_42) != iProver_top
    | m1_pre_topc(sK2,X0_42) != iProver_top
    | m1_pre_topc(sK1,X0_42) != iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2519])).

cnf(c_23,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_27,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_29,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1394,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1392])).

cnf(c_1465,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1463])).

cnf(c_1386,plain,
    ( ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,X2_42),X3_42)
    | ~ m1_pre_topc(sK2,X3_42)
    | ~ m1_pre_topc(sK1,X3_42)
    | v2_struct_0(X3_42)
    | v2_struct_0(k2_tsep_1(X0_42,X1_42,X2_42))
    | ~ v1_pre_topc(k2_tsep_1(X0_42,X1_42,X2_42))
    | ~ l1_pre_topc(X3_42)
    | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != u1_struct_0(k2_tsep_1(X0_42,X1_42,X2_42))
    | k2_tsep_1(X3_42,sK1,sK2) = k2_tsep_1(X0_42,X1_42,X2_42) ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_1629,plain,
    ( ~ m1_pre_topc(k2_tsep_1(X0_42,sK1,sK2),X1_42)
    | ~ m1_pre_topc(sK2,X1_42)
    | ~ m1_pre_topc(sK1,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(k2_tsep_1(X0_42,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(X0_42,sK1,sK2))
    | ~ l1_pre_topc(X1_42)
    | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != u1_struct_0(k2_tsep_1(X0_42,sK1,sK2))
    | k2_tsep_1(X1_42,sK1,sK2) = k2_tsep_1(X0_42,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1386])).

cnf(c_2184,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0_42)
    | ~ m1_pre_topc(sK2,X0_42)
    | ~ m1_pre_topc(sK1,X0_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(X0_42)
    | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | k2_tsep_1(X0_42,sK1,sK2) = k2_tsep_1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1629])).

cnf(c_2185,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | k2_tsep_1(X0_42,sK1,sK2) = k2_tsep_1(sK0,sK1,sK2)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0_42) != iProver_top
    | m1_pre_topc(sK2,X0_42) != iProver_top
    | m1_pre_topc(sK1,X0_42) != iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2184])).

cnf(c_2934,plain,
    ( k2_tsep_1(X0_42,sK1,sK2) = k2_tsep_1(sK0,sK1,sK2)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0_42) != iProver_top
    | m1_pre_topc(sK2,X0_42) != iProver_top
    | m1_pre_topc(sK1,X0_42) != iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2533,c_22,c_23,c_20,c_25,c_19,c_26,c_18,c_27,c_17,c_28,c_16,c_29,c_918,c_1393,c_1394,c_1427,c_1464,c_1465,c_1480,c_1617,c_2185])).

cnf(c_2944,plain,
    ( k2_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1,sK2) = k2_tsep_1(sK0,sK1,sK2)
    | m1_pre_topc(sK2,k2_tsep_1(sK0,sK1,sK2)) != iProver_top
    | m1_pre_topc(sK1,k2_tsep_1(sK0,sK1,sK2)) != iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) = iProver_top
    | l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1215,c_2934])).

cnf(c_3156,plain,
    ( m1_pre_topc(sK1,k2_tsep_1(sK0,sK1,sK2)) != iProver_top
    | m1_pre_topc(sK2,k2_tsep_1(sK0,sK1,sK2)) != iProver_top
    | k2_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1,sK2) = k2_tsep_1(sK0,sK1,sK2)
    | l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2944,c_23,c_25,c_26,c_27,c_28,c_29,c_1465])).

cnf(c_3157,plain,
    ( k2_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1,sK2) = k2_tsep_1(sK0,sK1,sK2)
    | m1_pre_topc(sK2,k2_tsep_1(sK0,sK1,sK2)) != iProver_top
    | m1_pre_topc(sK1,k2_tsep_1(sK0,sK1,sK2)) != iProver_top
    | l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3156])).

cnf(c_2532,plain,
    ( k2_tsep_1(X0_42,sK1,sK2) = k2_tsep_1(sK3,sK1,sK2)
    | m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0_42) != iProver_top
    | m1_pre_topc(sK2,X0_42) != iProver_top
    | m1_pre_topc(sK1,X0_42) != iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v2_struct_0(k2_tsep_1(sK3,sK1,sK2)) = iProver_top
    | v1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_2237,c_2519])).

cnf(c_33,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1897,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ v2_struct_0(k2_tsep_1(sK3,sK1,sK2))
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1462])).

cnf(c_1898,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK1,sK3) != iProver_top
    | v2_struct_0(k2_tsep_1(sK3,sK1,sK2)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1897])).

cnf(c_2571,plain,
    ( v2_struct_0(X0_42) = iProver_top
    | m1_pre_topc(sK1,X0_42) != iProver_top
    | m1_pre_topc(sK2,X0_42) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0_42) != iProver_top
    | k2_tsep_1(X0_42,sK1,sK2) = k2_tsep_1(sK3,sK1,sK2)
    | v1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2532,c_25,c_26,c_28,c_30,c_32,c_33,c_1510,c_1898])).

cnf(c_2572,plain,
    ( k2_tsep_1(X0_42,sK1,sK2) = k2_tsep_1(sK3,sK1,sK2)
    | m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0_42) != iProver_top
    | m1_pre_topc(sK2,X0_42) != iProver_top
    | m1_pre_topc(sK1,X0_42) != iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(renaming,[status(thm)],[c_2571])).

cnf(c_2584,plain,
    ( k2_tsep_1(k2_tsep_1(sK3,sK1,sK2),sK1,sK2) = k2_tsep_1(sK3,sK1,sK2)
    | m1_pre_topc(sK2,k2_tsep_1(sK3,sK1,sK2)) != iProver_top
    | m1_pre_topc(sK1,k2_tsep_1(sK3,sK1,sK2)) != iProver_top
    | v2_struct_0(k2_tsep_1(sK3,sK1,sK2)) = iProver_top
    | v1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) != iProver_top
    | l1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1215,c_2572])).

cnf(c_2924,plain,
    ( m1_pre_topc(sK1,k2_tsep_1(sK3,sK1,sK2)) != iProver_top
    | m1_pre_topc(sK2,k2_tsep_1(sK3,sK1,sK2)) != iProver_top
    | k2_tsep_1(k2_tsep_1(sK3,sK1,sK2),sK1,sK2) = k2_tsep_1(sK3,sK1,sK2)
    | v1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) != iProver_top
    | l1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2584,c_25,c_26,c_28,c_30,c_32,c_33,c_1510,c_1898])).

cnf(c_2925,plain,
    ( k2_tsep_1(k2_tsep_1(sK3,sK1,sK2),sK1,sK2) = k2_tsep_1(sK3,sK1,sK2)
    | m1_pre_topc(sK2,k2_tsep_1(sK3,sK1,sK2)) != iProver_top
    | m1_pre_topc(sK1,k2_tsep_1(sK3,sK1,sK2)) != iProver_top
    | v1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) != iProver_top
    | l1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2924])).

cnf(c_1956,plain,
    ( u1_struct_0(k2_tsep_1(X0_42,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2))
    | m1_pre_topc(sK2,X0_42) != iProver_top
    | m1_pre_topc(sK1,X0_42) != iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1953,c_1808])).

cnf(c_2324,plain,
    ( u1_struct_0(k2_tsep_1(X0_42,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | m1_pre_topc(sK2,X0_42) != iProver_top
    | m1_pre_topc(sK1,X0_42) != iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1956,c_2237])).

cnf(c_1821,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK2,sK1,sK2))
    | m1_pre_topc(sK1,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1215,c_1808])).

cnf(c_1508,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1217,c_1211])).

cnf(c_2315,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK2,sK1,sK2))
    | m1_pre_topc(sK1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1821,c_25,c_28,c_1508,c_1510])).

cnf(c_2319,plain,
    ( u1_struct_0(k2_tsep_1(sK2,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | m1_pre_topc(sK1,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2315,c_2234])).

cnf(c_1212,plain,
    ( m1_pre_topc(X0_42,X1_42) != iProver_top
    | m1_pre_topc(X2_42,X1_42) != iProver_top
    | m1_pre_topc(k2_tsep_1(X1_42,X0_42,X2_42),X1_42) = iProver_top
    | v2_struct_0(X1_42) = iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v2_struct_0(X2_42) = iProver_top
    | l1_pre_topc(X1_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_877])).

cnf(c_2000,plain,
    ( m1_pre_topc(X0_42,X1_42) != iProver_top
    | m1_pre_topc(X2_42,X1_42) != iProver_top
    | v2_struct_0(X1_42) = iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v2_struct_0(X2_42) = iProver_top
    | l1_pre_topc(X1_42) != iProver_top
    | l1_pre_topc(k2_tsep_1(X1_42,X0_42,X2_42)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1211])).

cnf(c_1730,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1510,c_25])).

cnf(c_871,negated_conjecture,
    ( m1_pre_topc(sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1218,plain,
    ( m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_871])).

cnf(c_1509,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_1211])).

cnf(c_1724,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1509,c_25,c_1510])).

cnf(c_1644,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1508,c_25,c_1510])).

cnf(c_1214,plain,
    ( m1_pre_topc(X0_42,X1_42) != iProver_top
    | m1_pre_topc(X2_42,X1_42) != iProver_top
    | v2_struct_0(X1_42) = iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v2_struct_0(X2_42) = iProver_top
    | v2_struct_0(k2_tsep_1(X1_42,X0_42,X2_42)) != iProver_top
    | l1_pre_topc(X1_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_875])).

cnf(c_1213,plain,
    ( m1_pre_topc(X0_42,X1_42) != iProver_top
    | m1_pre_topc(X2_42,X1_42) != iProver_top
    | v2_struct_0(X1_42) = iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v2_struct_0(X2_42) = iProver_top
    | v1_pre_topc(k2_tsep_1(X1_42,X0_42,X2_42)) = iProver_top
    | l1_pre_topc(X1_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_876])).

cnf(c_10,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_873,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1216,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_873])).

cnf(c_869,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1220,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_869])).

cnf(c_867,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1222,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_867])).

cnf(c_866,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1223,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_866])).

cnf(c_865,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1224,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_865])).

cnf(c_864,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1225,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_864])).

cnf(c_863,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1226,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_863])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:37:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.09/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.09/0.99  
% 2.09/0.99  ------  iProver source info
% 2.09/0.99  
% 2.09/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.09/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.09/0.99  git: non_committed_changes: false
% 2.09/0.99  git: last_make_outside_of_git: false
% 2.09/0.99  
% 2.09/0.99  ------ 
% 2.09/0.99  
% 2.09/0.99  ------ Input Options
% 2.09/0.99  
% 2.09/0.99  --out_options                           all
% 2.09/0.99  --tptp_safe_out                         true
% 2.09/0.99  --problem_path                          ""
% 2.09/0.99  --include_path                          ""
% 2.09/0.99  --clausifier                            res/vclausify_rel
% 2.09/0.99  --clausifier_options                    --mode clausify
% 2.09/0.99  --stdin                                 false
% 2.09/0.99  --stats_out                             all
% 2.09/0.99  
% 2.09/0.99  ------ General Options
% 2.09/0.99  
% 2.09/0.99  --fof                                   false
% 2.09/0.99  --time_out_real                         305.
% 2.09/0.99  --time_out_virtual                      -1.
% 2.09/0.99  --symbol_type_check                     false
% 2.09/0.99  --clausify_out                          false
% 2.09/0.99  --sig_cnt_out                           false
% 2.09/0.99  --trig_cnt_out                          false
% 2.09/0.99  --trig_cnt_out_tolerance                1.
% 2.09/0.99  --trig_cnt_out_sk_spl                   false
% 2.09/0.99  --abstr_cl_out                          false
% 2.09/0.99  
% 2.09/0.99  ------ Global Options
% 2.09/0.99  
% 2.09/0.99  --schedule                              default
% 2.09/0.99  --add_important_lit                     false
% 2.09/0.99  --prop_solver_per_cl                    1000
% 2.09/0.99  --min_unsat_core                        false
% 2.09/0.99  --soft_assumptions                      false
% 2.09/0.99  --soft_lemma_size                       3
% 2.09/0.99  --prop_impl_unit_size                   0
% 2.09/0.99  --prop_impl_unit                        []
% 2.09/0.99  --share_sel_clauses                     true
% 2.09/0.99  --reset_solvers                         false
% 2.09/0.99  --bc_imp_inh                            [conj_cone]
% 2.09/0.99  --conj_cone_tolerance                   3.
% 2.09/0.99  --extra_neg_conj                        none
% 2.09/0.99  --large_theory_mode                     true
% 2.09/0.99  --prolific_symb_bound                   200
% 2.09/0.99  --lt_threshold                          2000
% 2.09/0.99  --clause_weak_htbl                      true
% 2.09/0.99  --gc_record_bc_elim                     false
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing Options
% 2.09/0.99  
% 2.09/0.99  --preprocessing_flag                    true
% 2.09/0.99  --time_out_prep_mult                    0.1
% 2.09/0.99  --splitting_mode                        input
% 2.09/0.99  --splitting_grd                         true
% 2.09/0.99  --splitting_cvd                         false
% 2.09/0.99  --splitting_cvd_svl                     false
% 2.09/0.99  --splitting_nvd                         32
% 2.09/0.99  --sub_typing                            true
% 2.09/0.99  --prep_gs_sim                           true
% 2.09/0.99  --prep_unflatten                        true
% 2.09/0.99  --prep_res_sim                          true
% 2.09/0.99  --prep_upred                            true
% 2.09/0.99  --prep_sem_filter                       exhaustive
% 2.09/0.99  --prep_sem_filter_out                   false
% 2.09/0.99  --pred_elim                             true
% 2.09/0.99  --res_sim_input                         true
% 2.09/0.99  --eq_ax_congr_red                       true
% 2.09/0.99  --pure_diseq_elim                       true
% 2.09/0.99  --brand_transform                       false
% 2.09/0.99  --non_eq_to_eq                          false
% 2.09/0.99  --prep_def_merge                        true
% 2.09/0.99  --prep_def_merge_prop_impl              false
% 2.09/0.99  --prep_def_merge_mbd                    true
% 2.09/0.99  --prep_def_merge_tr_red                 false
% 2.09/0.99  --prep_def_merge_tr_cl                  false
% 2.09/0.99  --smt_preprocessing                     true
% 2.09/0.99  --smt_ac_axioms                         fast
% 2.09/0.99  --preprocessed_out                      false
% 2.09/0.99  --preprocessed_stats                    false
% 2.09/0.99  
% 2.09/0.99  ------ Abstraction refinement Options
% 2.09/0.99  
% 2.09/0.99  --abstr_ref                             []
% 2.09/0.99  --abstr_ref_prep                        false
% 2.09/0.99  --abstr_ref_until_sat                   false
% 2.09/0.99  --abstr_ref_sig_restrict                funpre
% 2.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.09/0.99  --abstr_ref_under                       []
% 2.09/0.99  
% 2.09/0.99  ------ SAT Options
% 2.09/0.99  
% 2.09/0.99  --sat_mode                              false
% 2.09/0.99  --sat_fm_restart_options                ""
% 2.09/0.99  --sat_gr_def                            false
% 2.09/0.99  --sat_epr_types                         true
% 2.09/0.99  --sat_non_cyclic_types                  false
% 2.09/0.99  --sat_finite_models                     false
% 2.09/0.99  --sat_fm_lemmas                         false
% 2.09/0.99  --sat_fm_prep                           false
% 2.09/0.99  --sat_fm_uc_incr                        true
% 2.09/0.99  --sat_out_model                         small
% 2.09/0.99  --sat_out_clauses                       false
% 2.09/0.99  
% 2.09/0.99  ------ QBF Options
% 2.09/0.99  
% 2.09/0.99  --qbf_mode                              false
% 2.09/0.99  --qbf_elim_univ                         false
% 2.09/0.99  --qbf_dom_inst                          none
% 2.09/0.99  --qbf_dom_pre_inst                      false
% 2.09/0.99  --qbf_sk_in                             false
% 2.09/0.99  --qbf_pred_elim                         true
% 2.09/0.99  --qbf_split                             512
% 2.09/0.99  
% 2.09/0.99  ------ BMC1 Options
% 2.09/0.99  
% 2.09/0.99  --bmc1_incremental                      false
% 2.09/0.99  --bmc1_axioms                           reachable_all
% 2.09/0.99  --bmc1_min_bound                        0
% 2.09/0.99  --bmc1_max_bound                        -1
% 2.09/0.99  --bmc1_max_bound_default                -1
% 2.09/0.99  --bmc1_symbol_reachability              true
% 2.09/0.99  --bmc1_property_lemmas                  false
% 2.09/0.99  --bmc1_k_induction                      false
% 2.09/0.99  --bmc1_non_equiv_states                 false
% 2.09/0.99  --bmc1_deadlock                         false
% 2.09/0.99  --bmc1_ucm                              false
% 2.09/0.99  --bmc1_add_unsat_core                   none
% 2.09/0.99  --bmc1_unsat_core_children              false
% 2.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.09/0.99  --bmc1_out_stat                         full
% 2.09/0.99  --bmc1_ground_init                      false
% 2.09/0.99  --bmc1_pre_inst_next_state              false
% 2.09/0.99  --bmc1_pre_inst_state                   false
% 2.09/0.99  --bmc1_pre_inst_reach_state             false
% 2.09/0.99  --bmc1_out_unsat_core                   false
% 2.09/0.99  --bmc1_aig_witness_out                  false
% 2.09/0.99  --bmc1_verbose                          false
% 2.09/0.99  --bmc1_dump_clauses_tptp                false
% 2.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.09/0.99  --bmc1_dump_file                        -
% 2.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.09/0.99  --bmc1_ucm_extend_mode                  1
% 2.09/0.99  --bmc1_ucm_init_mode                    2
% 2.09/0.99  --bmc1_ucm_cone_mode                    none
% 2.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.09/0.99  --bmc1_ucm_relax_model                  4
% 2.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.09/0.99  --bmc1_ucm_layered_model                none
% 2.09/0.99  --bmc1_ucm_max_lemma_size               10
% 2.09/0.99  
% 2.09/0.99  ------ AIG Options
% 2.09/0.99  
% 2.09/0.99  --aig_mode                              false
% 2.09/0.99  
% 2.09/0.99  ------ Instantiation Options
% 2.09/0.99  
% 2.09/0.99  --instantiation_flag                    true
% 2.09/0.99  --inst_sos_flag                         false
% 2.09/0.99  --inst_sos_phase                        true
% 2.09/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel_side                     num_symb
% 2.09/0.99  --inst_solver_per_active                1400
% 2.09/0.99  --inst_solver_calls_frac                1.
% 2.09/0.99  --inst_passive_queue_type               priority_queues
% 2.09/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.09/0.99  --inst_passive_queues_freq              [25;2]
% 2.09/0.99  --inst_dismatching                      true
% 2.09/0.99  --inst_eager_unprocessed_to_passive     true
% 2.09/0.99  --inst_prop_sim_given                   true
% 2.09/0.99  --inst_prop_sim_new                     false
% 2.09/0.99  --inst_subs_new                         false
% 2.09/0.99  --inst_eq_res_simp                      false
% 2.09/0.99  --inst_subs_given                       false
% 2.09/0.99  --inst_orphan_elimination               true
% 2.09/0.99  --inst_learning_loop_flag               true
% 2.09/0.99  --inst_learning_start                   3000
% 2.09/0.99  --inst_learning_factor                  2
% 2.09/0.99  --inst_start_prop_sim_after_learn       3
% 2.09/0.99  --inst_sel_renew                        solver
% 2.09/0.99  --inst_lit_activity_flag                true
% 2.09/0.99  --inst_restr_to_given                   false
% 2.09/0.99  --inst_activity_threshold               500
% 2.09/0.99  --inst_out_proof                        true
% 2.09/0.99  
% 2.09/0.99  ------ Resolution Options
% 2.09/0.99  
% 2.09/0.99  --resolution_flag                       true
% 2.09/0.99  --res_lit_sel                           adaptive
% 2.09/0.99  --res_lit_sel_side                      none
% 2.09/0.99  --res_ordering                          kbo
% 2.09/0.99  --res_to_prop_solver                    active
% 2.09/0.99  --res_prop_simpl_new                    false
% 2.09/0.99  --res_prop_simpl_given                  true
% 2.09/0.99  --res_passive_queue_type                priority_queues
% 2.09/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.09/0.99  --res_passive_queues_freq               [15;5]
% 2.09/0.99  --res_forward_subs                      full
% 2.09/0.99  --res_backward_subs                     full
% 2.09/0.99  --res_forward_subs_resolution           true
% 2.09/0.99  --res_backward_subs_resolution          true
% 2.09/0.99  --res_orphan_elimination                true
% 2.09/0.99  --res_time_limit                        2.
% 2.09/0.99  --res_out_proof                         true
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Options
% 2.09/0.99  
% 2.09/0.99  --superposition_flag                    true
% 2.09/0.99  --sup_passive_queue_type                priority_queues
% 2.09/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.09/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.09/0.99  --demod_completeness_check              fast
% 2.09/0.99  --demod_use_ground                      true
% 2.09/0.99  --sup_to_prop_solver                    passive
% 2.09/0.99  --sup_prop_simpl_new                    true
% 2.09/0.99  --sup_prop_simpl_given                  true
% 2.09/0.99  --sup_fun_splitting                     false
% 2.09/0.99  --sup_smt_interval                      50000
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Simplification Setup
% 2.09/0.99  
% 2.09/0.99  --sup_indices_passive                   []
% 2.09/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.09/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_full_bw                           [BwDemod]
% 2.09/0.99  --sup_immed_triv                        [TrivRules]
% 2.09/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.09/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_immed_bw_main                     []
% 2.09/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.09/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  
% 2.09/0.99  ------ Combination Options
% 2.09/0.99  
% 2.09/0.99  --comb_res_mult                         3
% 2.09/0.99  --comb_sup_mult                         2
% 2.09/0.99  --comb_inst_mult                        10
% 2.09/0.99  
% 2.09/0.99  ------ Debug Options
% 2.09/0.99  
% 2.09/0.99  --dbg_backtrace                         false
% 2.09/0.99  --dbg_dump_prop_clauses                 false
% 2.09/0.99  --dbg_dump_prop_clauses_file            -
% 2.09/0.99  --dbg_out_stat                          false
% 2.09/0.99  ------ Parsing...
% 2.09/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.09/0.99  ------ Proving...
% 2.09/0.99  ------ Problem Properties 
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  clauses                                 18
% 2.09/0.99  conjectures                             11
% 2.09/0.99  EPR                                     12
% 2.09/0.99  Horn                                    13
% 2.09/0.99  unary                                   11
% 2.09/0.99  binary                                  1
% 2.09/0.99  lits                                    54
% 2.09/0.99  lits eq                                 3
% 2.09/0.99  fd_pure                                 0
% 2.09/0.99  fd_pseudo                               0
% 2.09/0.99  fd_cond                                 0
% 2.09/0.99  fd_pseudo_cond                          1
% 2.09/0.99  AC symbols                              0
% 2.09/0.99  
% 2.09/0.99  ------ Schedule dynamic 5 is on 
% 2.09/0.99  
% 2.09/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  ------ 
% 2.09/0.99  Current options:
% 2.09/0.99  ------ 
% 2.09/0.99  
% 2.09/0.99  ------ Input Options
% 2.09/0.99  
% 2.09/0.99  --out_options                           all
% 2.09/0.99  --tptp_safe_out                         true
% 2.09/0.99  --problem_path                          ""
% 2.09/0.99  --include_path                          ""
% 2.09/0.99  --clausifier                            res/vclausify_rel
% 2.09/0.99  --clausifier_options                    --mode clausify
% 2.09/0.99  --stdin                                 false
% 2.09/0.99  --stats_out                             all
% 2.09/0.99  
% 2.09/0.99  ------ General Options
% 2.09/0.99  
% 2.09/0.99  --fof                                   false
% 2.09/0.99  --time_out_real                         305.
% 2.09/0.99  --time_out_virtual                      -1.
% 2.09/0.99  --symbol_type_check                     false
% 2.09/0.99  --clausify_out                          false
% 2.09/0.99  --sig_cnt_out                           false
% 2.09/0.99  --trig_cnt_out                          false
% 2.09/0.99  --trig_cnt_out_tolerance                1.
% 2.09/0.99  --trig_cnt_out_sk_spl                   false
% 2.09/0.99  --abstr_cl_out                          false
% 2.09/0.99  
% 2.09/0.99  ------ Global Options
% 2.09/0.99  
% 2.09/0.99  --schedule                              default
% 2.09/0.99  --add_important_lit                     false
% 2.09/0.99  --prop_solver_per_cl                    1000
% 2.09/0.99  --min_unsat_core                        false
% 2.09/0.99  --soft_assumptions                      false
% 2.09/0.99  --soft_lemma_size                       3
% 2.09/0.99  --prop_impl_unit_size                   0
% 2.09/0.99  --prop_impl_unit                        []
% 2.09/0.99  --share_sel_clauses                     true
% 2.09/0.99  --reset_solvers                         false
% 2.09/0.99  --bc_imp_inh                            [conj_cone]
% 2.09/0.99  --conj_cone_tolerance                   3.
% 2.09/0.99  --extra_neg_conj                        none
% 2.09/0.99  --large_theory_mode                     true
% 2.09/0.99  --prolific_symb_bound                   200
% 2.09/0.99  --lt_threshold                          2000
% 2.09/0.99  --clause_weak_htbl                      true
% 2.09/0.99  --gc_record_bc_elim                     false
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing Options
% 2.09/0.99  
% 2.09/0.99  --preprocessing_flag                    true
% 2.09/0.99  --time_out_prep_mult                    0.1
% 2.09/0.99  --splitting_mode                        input
% 2.09/0.99  --splitting_grd                         true
% 2.09/0.99  --splitting_cvd                         false
% 2.09/0.99  --splitting_cvd_svl                     false
% 2.09/0.99  --splitting_nvd                         32
% 2.09/0.99  --sub_typing                            true
% 2.09/0.99  --prep_gs_sim                           true
% 2.09/0.99  --prep_unflatten                        true
% 2.09/0.99  --prep_res_sim                          true
% 2.09/0.99  --prep_upred                            true
% 2.09/0.99  --prep_sem_filter                       exhaustive
% 2.09/0.99  --prep_sem_filter_out                   false
% 2.09/0.99  --pred_elim                             true
% 2.09/0.99  --res_sim_input                         true
% 2.09/0.99  --eq_ax_congr_red                       true
% 2.09/0.99  --pure_diseq_elim                       true
% 2.09/0.99  --brand_transform                       false
% 2.09/0.99  --non_eq_to_eq                          false
% 2.09/0.99  --prep_def_merge                        true
% 2.09/0.99  --prep_def_merge_prop_impl              false
% 2.09/0.99  --prep_def_merge_mbd                    true
% 2.09/0.99  --prep_def_merge_tr_red                 false
% 2.09/0.99  --prep_def_merge_tr_cl                  false
% 2.09/0.99  --smt_preprocessing                     true
% 2.09/0.99  --smt_ac_axioms                         fast
% 2.09/0.99  --preprocessed_out                      false
% 2.09/0.99  --preprocessed_stats                    false
% 2.09/0.99  
% 2.09/0.99  ------ Abstraction refinement Options
% 2.09/0.99  
% 2.09/0.99  --abstr_ref                             []
% 2.09/0.99  --abstr_ref_prep                        false
% 2.09/0.99  --abstr_ref_until_sat                   false
% 2.09/0.99  --abstr_ref_sig_restrict                funpre
% 2.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.09/0.99  --abstr_ref_under                       []
% 2.09/0.99  
% 2.09/0.99  ------ SAT Options
% 2.09/0.99  
% 2.09/0.99  --sat_mode                              false
% 2.09/0.99  --sat_fm_restart_options                ""
% 2.09/0.99  --sat_gr_def                            false
% 2.09/0.99  --sat_epr_types                         true
% 2.09/0.99  --sat_non_cyclic_types                  false
% 2.09/0.99  --sat_finite_models                     false
% 2.09/0.99  --sat_fm_lemmas                         false
% 2.09/0.99  --sat_fm_prep                           false
% 2.09/0.99  --sat_fm_uc_incr                        true
% 2.09/0.99  --sat_out_model                         small
% 2.09/0.99  --sat_out_clauses                       false
% 2.09/0.99  
% 2.09/0.99  ------ QBF Options
% 2.09/0.99  
% 2.09/0.99  --qbf_mode                              false
% 2.09/0.99  --qbf_elim_univ                         false
% 2.09/0.99  --qbf_dom_inst                          none
% 2.09/0.99  --qbf_dom_pre_inst                      false
% 2.09/0.99  --qbf_sk_in                             false
% 2.09/0.99  --qbf_pred_elim                         true
% 2.09/0.99  --qbf_split                             512
% 2.09/0.99  
% 2.09/0.99  ------ BMC1 Options
% 2.09/0.99  
% 2.09/0.99  --bmc1_incremental                      false
% 2.09/0.99  --bmc1_axioms                           reachable_all
% 2.09/0.99  --bmc1_min_bound                        0
% 2.09/0.99  --bmc1_max_bound                        -1
% 2.09/0.99  --bmc1_max_bound_default                -1
% 2.09/0.99  --bmc1_symbol_reachability              true
% 2.09/0.99  --bmc1_property_lemmas                  false
% 2.09/0.99  --bmc1_k_induction                      false
% 2.09/0.99  --bmc1_non_equiv_states                 false
% 2.09/0.99  --bmc1_deadlock                         false
% 2.09/0.99  --bmc1_ucm                              false
% 2.09/0.99  --bmc1_add_unsat_core                   none
% 2.09/0.99  --bmc1_unsat_core_children              false
% 2.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.09/0.99  --bmc1_out_stat                         full
% 2.09/0.99  --bmc1_ground_init                      false
% 2.09/0.99  --bmc1_pre_inst_next_state              false
% 2.09/0.99  --bmc1_pre_inst_state                   false
% 2.09/0.99  --bmc1_pre_inst_reach_state             false
% 2.09/0.99  --bmc1_out_unsat_core                   false
% 2.09/0.99  --bmc1_aig_witness_out                  false
% 2.09/0.99  --bmc1_verbose                          false
% 2.09/0.99  --bmc1_dump_clauses_tptp                false
% 2.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.09/0.99  --bmc1_dump_file                        -
% 2.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.09/0.99  --bmc1_ucm_extend_mode                  1
% 2.09/0.99  --bmc1_ucm_init_mode                    2
% 2.09/0.99  --bmc1_ucm_cone_mode                    none
% 2.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.09/0.99  --bmc1_ucm_relax_model                  4
% 2.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.09/0.99  --bmc1_ucm_layered_model                none
% 2.09/0.99  --bmc1_ucm_max_lemma_size               10
% 2.09/0.99  
% 2.09/0.99  ------ AIG Options
% 2.09/0.99  
% 2.09/0.99  --aig_mode                              false
% 2.09/0.99  
% 2.09/0.99  ------ Instantiation Options
% 2.09/0.99  
% 2.09/0.99  --instantiation_flag                    true
% 2.09/0.99  --inst_sos_flag                         false
% 2.09/0.99  --inst_sos_phase                        true
% 2.09/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel_side                     none
% 2.09/0.99  --inst_solver_per_active                1400
% 2.09/0.99  --inst_solver_calls_frac                1.
% 2.09/0.99  --inst_passive_queue_type               priority_queues
% 2.09/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.09/0.99  --inst_passive_queues_freq              [25;2]
% 2.09/0.99  --inst_dismatching                      true
% 2.09/0.99  --inst_eager_unprocessed_to_passive     true
% 2.09/0.99  --inst_prop_sim_given                   true
% 2.09/0.99  --inst_prop_sim_new                     false
% 2.09/0.99  --inst_subs_new                         false
% 2.09/0.99  --inst_eq_res_simp                      false
% 2.09/0.99  --inst_subs_given                       false
% 2.09/0.99  --inst_orphan_elimination               true
% 2.09/0.99  --inst_learning_loop_flag               true
% 2.09/0.99  --inst_learning_start                   3000
% 2.09/0.99  --inst_learning_factor                  2
% 2.09/0.99  --inst_start_prop_sim_after_learn       3
% 2.09/0.99  --inst_sel_renew                        solver
% 2.09/0.99  --inst_lit_activity_flag                true
% 2.09/0.99  --inst_restr_to_given                   false
% 2.09/0.99  --inst_activity_threshold               500
% 2.09/0.99  --inst_out_proof                        true
% 2.09/0.99  
% 2.09/0.99  ------ Resolution Options
% 2.09/0.99  
% 2.09/0.99  --resolution_flag                       false
% 2.09/0.99  --res_lit_sel                           adaptive
% 2.09/0.99  --res_lit_sel_side                      none
% 2.09/0.99  --res_ordering                          kbo
% 2.09/0.99  --res_to_prop_solver                    active
% 2.09/0.99  --res_prop_simpl_new                    false
% 2.09/0.99  --res_prop_simpl_given                  true
% 2.09/0.99  --res_passive_queue_type                priority_queues
% 2.09/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.09/0.99  --res_passive_queues_freq               [15;5]
% 2.09/0.99  --res_forward_subs                      full
% 2.09/0.99  --res_backward_subs                     full
% 2.09/0.99  --res_forward_subs_resolution           true
% 2.09/0.99  --res_backward_subs_resolution          true
% 2.09/0.99  --res_orphan_elimination                true
% 2.09/0.99  --res_time_limit                        2.
% 2.09/0.99  --res_out_proof                         true
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Options
% 2.09/0.99  
% 2.09/0.99  --superposition_flag                    true
% 2.09/0.99  --sup_passive_queue_type                priority_queues
% 2.09/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.09/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.09/0.99  --demod_completeness_check              fast
% 2.09/0.99  --demod_use_ground                      true
% 2.09/0.99  --sup_to_prop_solver                    passive
% 2.09/0.99  --sup_prop_simpl_new                    true
% 2.09/0.99  --sup_prop_simpl_given                  true
% 2.09/0.99  --sup_fun_splitting                     false
% 2.09/0.99  --sup_smt_interval                      50000
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Simplification Setup
% 2.09/0.99  
% 2.09/0.99  --sup_indices_passive                   []
% 2.09/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.09/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_full_bw                           [BwDemod]
% 2.09/0.99  --sup_immed_triv                        [TrivRules]
% 2.09/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.09/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_immed_bw_main                     []
% 2.09/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.09/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  
% 2.09/0.99  ------ Combination Options
% 2.09/0.99  
% 2.09/0.99  --comb_res_mult                         3
% 2.09/0.99  --comb_sup_mult                         2
% 2.09/0.99  --comb_inst_mult                        10
% 2.09/0.99  
% 2.09/0.99  ------ Debug Options
% 2.09/0.99  
% 2.09/0.99  --dbg_backtrace                         false
% 2.09/0.99  --dbg_dump_prop_clauses                 false
% 2.09/0.99  --dbg_dump_prop_clauses_file            -
% 2.09/0.99  --dbg_out_stat                          false
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  ------ Proving...
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  % SZS output start Saturation for theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  fof(f7,conjecture,(
% 2.09/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f8,negated_conjecture,(
% 2.09/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 2.09/0.99    inference(negated_conjecture,[],[f7])).
% 2.09/0.99  
% 2.09/0.99  fof(f19,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f8])).
% 2.09/0.99  
% 2.09/0.99  fof(f20,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f19])).
% 2.09/0.99  
% 2.09/0.99  fof(f26,plain,(
% 2.09/0.99    ( ! [X2,X0,X1] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k2_tsep_1(X0,X1,X2),sK3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK3) & m1_pre_topc(X1,sK3) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f25,plain,(
% 2.09/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,sK2),X3) & ~r1_tsep_1(X1,sK2) & m1_pre_topc(sK2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f24,plain,(
% 2.09/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,sK1,X2),X3) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f23,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f27,plain,(
% 2.09/0.99    (((~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK1,sK3) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f26,f25,f24,f23])).
% 2.09/0.99  
% 2.09/0.99  fof(f39,plain,(
% 2.09/0.99    v2_pre_topc(sK0)),
% 2.09/0.99    inference(cnf_transformation,[],[f27])).
% 2.09/0.99  
% 2.09/0.99  fof(f1,axiom,(
% 2.09/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f9,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f1])).
% 2.09/0.99  
% 2.09/0.99  fof(f10,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.09/0.99    inference(flattening,[],[f9])).
% 2.09/0.99  
% 2.09/0.99  fof(f28,plain,(
% 2.09/0.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f10])).
% 2.09/0.99  
% 2.09/0.99  fof(f5,axiom,(
% 2.09/0.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f16,plain,(
% 2.09/0.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(ennf_transformation,[],[f5])).
% 2.09/0.99  
% 2.09/0.99  fof(f35,plain,(
% 2.09/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f16])).
% 2.09/0.99  
% 2.09/0.99  fof(f48,plain,(
% 2.09/0.99    m1_pre_topc(sK2,sK3)),
% 2.09/0.99    inference(cnf_transformation,[],[f27])).
% 2.09/0.99  
% 2.09/0.99  fof(f3,axiom,(
% 2.09/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f12,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f3])).
% 2.09/0.99  
% 2.09/0.99  fof(f13,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f12])).
% 2.09/0.99  
% 2.09/0.99  fof(f21,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(nnf_transformation,[],[f13])).
% 2.09/0.99  
% 2.09/0.99  fof(f30,plain,(
% 2.09/0.99    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f21])).
% 2.09/0.99  
% 2.09/0.99  fof(f51,plain,(
% 2.09/0.99    ( ! [X2,X0,X1] : (u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(equality_resolution,[],[f30])).
% 2.09/0.99  
% 2.09/0.99  fof(f49,plain,(
% 2.09/0.99    ~r1_tsep_1(sK1,sK2)),
% 2.09/0.99    inference(cnf_transformation,[],[f27])).
% 2.09/0.99  
% 2.09/0.99  fof(f41,plain,(
% 2.09/0.99    ~v2_struct_0(sK1)),
% 2.09/0.99    inference(cnf_transformation,[],[f27])).
% 2.09/0.99  
% 2.09/0.99  fof(f43,plain,(
% 2.09/0.99    ~v2_struct_0(sK2)),
% 2.09/0.99    inference(cnf_transformation,[],[f27])).
% 2.09/0.99  
% 2.09/0.99  fof(f4,axiom,(
% 2.09/0.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f14,plain,(
% 2.09/0.99    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f4])).
% 2.09/0.99  
% 2.09/0.99  fof(f15,plain,(
% 2.09/0.99    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f14])).
% 2.09/0.99  
% 2.09/0.99  fof(f33,plain,(
% 2.09/0.99    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f15])).
% 2.09/0.99  
% 2.09/0.99  fof(f34,plain,(
% 2.09/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f15])).
% 2.09/0.99  
% 2.09/0.99  fof(f32,plain,(
% 2.09/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f15])).
% 2.09/0.99  
% 2.09/0.99  fof(f40,plain,(
% 2.09/0.99    l1_pre_topc(sK0)),
% 2.09/0.99    inference(cnf_transformation,[],[f27])).
% 2.09/0.99  
% 2.09/0.99  fof(f45,plain,(
% 2.09/0.99    ~v2_struct_0(sK3)),
% 2.09/0.99    inference(cnf_transformation,[],[f27])).
% 2.09/0.99  
% 2.09/0.99  fof(f47,plain,(
% 2.09/0.99    m1_pre_topc(sK1,sK3)),
% 2.09/0.99    inference(cnf_transformation,[],[f27])).
% 2.09/0.99  
% 2.09/0.99  fof(f46,plain,(
% 2.09/0.99    m1_pre_topc(sK3,sK0)),
% 2.09/0.99    inference(cnf_transformation,[],[f27])).
% 2.09/0.99  
% 2.09/0.99  fof(f2,axiom,(
% 2.09/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f11,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(ennf_transformation,[],[f2])).
% 2.09/0.99  
% 2.09/0.99  fof(f29,plain,(
% 2.09/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f11])).
% 2.09/0.99  
% 2.09/0.99  fof(f31,plain,(
% 2.09/0.99    ( ! [X2,X0,X3,X1] : (k2_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f21])).
% 2.09/0.99  
% 2.09/0.99  fof(f44,plain,(
% 2.09/0.99    m1_pre_topc(sK2,sK0)),
% 2.09/0.99    inference(cnf_transformation,[],[f27])).
% 2.09/0.99  
% 2.09/0.99  fof(f38,plain,(
% 2.09/0.99    ~v2_struct_0(sK0)),
% 2.09/0.99    inference(cnf_transformation,[],[f27])).
% 2.09/0.99  
% 2.09/0.99  fof(f42,plain,(
% 2.09/0.99    m1_pre_topc(sK1,sK0)),
% 2.09/0.99    inference(cnf_transformation,[],[f27])).
% 2.09/0.99  
% 2.09/0.99  fof(f50,plain,(
% 2.09/0.99    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 2.09/0.99    inference(cnf_transformation,[],[f27])).
% 2.09/0.99  
% 2.09/0.99  cnf(c_211,plain,
% 2.09/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.09/0.99      theory(equality) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_210,plain,
% 2.09/0.99      ( ~ r1_tsep_1(X0,X1) | r1_tsep_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.09/0.99      theory(equality) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_202,plain,
% 2.09/0.99      ( ~ v2_pre_topc(X0) | v2_pre_topc(X1) | X1 != X0 ),
% 2.09/0.99      theory(equality) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_879,plain,( X0_2 = X0_2 ),theory(equality) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_21,negated_conjecture,
% 2.09/0.99      ( v2_pre_topc(sK0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_0,plain,
% 2.09/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.09/0.99      | ~ l1_pre_topc(X1)
% 2.09/0.99      | ~ v2_pre_topc(X1)
% 2.09/0.99      | v2_pre_topc(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f28]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_7,plain,
% 2.09/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_874,plain,
% 2.09/0.99      ( m1_pre_topc(X0_42,X0_42) | ~ l1_pre_topc(X0_42) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1215,plain,
% 2.09/0.99      ( m1_pre_topc(X0_42,X0_42) = iProver_top
% 2.09/0.99      | l1_pre_topc(X0_42) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_874]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_12,negated_conjecture,
% 2.09/0.99      ( m1_pre_topc(sK2,sK3) ),
% 2.09/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_872,negated_conjecture,
% 2.09/0.99      ( m1_pre_topc(sK2,sK3) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1217,plain,
% 2.09/0.99      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_872]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_3,plain,
% 2.09/0.99      ( r1_tsep_1(X0,X1)
% 2.09/0.99      | ~ m1_pre_topc(X0,X2)
% 2.09/0.99      | ~ m1_pre_topc(X1,X2)
% 2.09/0.99      | ~ m1_pre_topc(k2_tsep_1(X2,X0,X1),X2)
% 2.09/0.99      | v2_struct_0(X2)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | v2_struct_0(k2_tsep_1(X2,X0,X1))
% 2.09/0.99      | ~ v1_pre_topc(k2_tsep_1(X2,X0,X1))
% 2.09/0.99      | ~ l1_pre_topc(X2)
% 2.09/0.99      | u1_struct_0(k2_tsep_1(X2,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 2.09/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_11,negated_conjecture,
% 2.09/0.99      ( ~ r1_tsep_1(sK1,sK2) ),
% 2.09/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_236,plain,
% 2.09/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.09/0.99      | ~ m1_pre_topc(X2,X1)
% 2.09/0.99      | ~ m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
% 2.09/0.99      | v2_struct_0(X2)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | v2_struct_0(k2_tsep_1(X1,X0,X2))
% 2.09/0.99      | ~ v1_pre_topc(k2_tsep_1(X1,X0,X2))
% 2.09/0.99      | ~ l1_pre_topc(X1)
% 2.09/0.99      | u1_struct_0(k2_tsep_1(X1,X0,X2)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X2))
% 2.09/0.99      | sK2 != X2
% 2.09/0.99      | sK1 != X0 ),
% 2.09/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_11]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_237,plain,
% 2.09/0.99      ( ~ m1_pre_topc(k2_tsep_1(X0,sK1,sK2),X0)
% 2.09/0.99      | ~ m1_pre_topc(sK2,X0)
% 2.09/0.99      | ~ m1_pre_topc(sK1,X0)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | v2_struct_0(k2_tsep_1(X0,sK1,sK2))
% 2.09/0.99      | v2_struct_0(sK2)
% 2.09/0.99      | v2_struct_0(sK1)
% 2.09/0.99      | ~ v1_pre_topc(k2_tsep_1(X0,sK1,sK2))
% 2.09/0.99      | ~ l1_pre_topc(X0)
% 2.09/0.99      | u1_struct_0(k2_tsep_1(X0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.09/0.99      inference(unflattening,[status(thm)],[c_236]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_19,negated_conjecture,
% 2.09/0.99      ( ~ v2_struct_0(sK1) ),
% 2.09/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_17,negated_conjecture,
% 2.09/0.99      ( ~ v2_struct_0(sK2) ),
% 2.09/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_241,plain,
% 2.09/0.99      ( ~ m1_pre_topc(k2_tsep_1(X0,sK1,sK2),X0)
% 2.09/0.99      | ~ m1_pre_topc(sK2,X0)
% 2.09/0.99      | ~ m1_pre_topc(sK1,X0)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | v2_struct_0(k2_tsep_1(X0,sK1,sK2))
% 2.09/0.99      | ~ v1_pre_topc(k2_tsep_1(X0,sK1,sK2))
% 2.09/0.99      | ~ l1_pre_topc(X0)
% 2.09/0.99      | u1_struct_0(k2_tsep_1(X0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_237,c_19,c_17]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_862,plain,
% 2.09/0.99      ( ~ m1_pre_topc(k2_tsep_1(X0_42,sK1,sK2),X0_42)
% 2.09/0.99      | ~ m1_pre_topc(sK2,X0_42)
% 2.09/0.99      | ~ m1_pre_topc(sK1,X0_42)
% 2.09/0.99      | v2_struct_0(X0_42)
% 2.09/0.99      | v2_struct_0(k2_tsep_1(X0_42,sK1,sK2))
% 2.09/0.99      | ~ v1_pre_topc(k2_tsep_1(X0_42,sK1,sK2))
% 2.09/0.99      | ~ l1_pre_topc(X0_42)
% 2.09/0.99      | u1_struct_0(k2_tsep_1(X0_42,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_241]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1227,plain,
% 2.09/0.99      ( u1_struct_0(k2_tsep_1(X0_42,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
% 2.09/0.99      | m1_pre_topc(k2_tsep_1(X0_42,sK1,sK2),X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK2,X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,X0_42) != iProver_top
% 2.09/0.99      | v2_struct_0(X0_42) = iProver_top
% 2.09/0.99      | v2_struct_0(k2_tsep_1(X0_42,sK1,sK2)) = iProver_top
% 2.09/0.99      | v1_pre_topc(k2_tsep_1(X0_42,sK1,sK2)) != iProver_top
% 2.09/0.99      | l1_pre_topc(X0_42) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_862]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_26,plain,
% 2.09/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_28,plain,
% 2.09/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_917,plain,
% 2.09/0.99      ( u1_struct_0(k2_tsep_1(X0_42,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
% 2.09/0.99      | m1_pre_topc(k2_tsep_1(X0_42,sK1,sK2),X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK2,X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,X0_42) != iProver_top
% 2.09/0.99      | v2_struct_0(X0_42) = iProver_top
% 2.09/0.99      | v2_struct_0(k2_tsep_1(X0_42,sK1,sK2)) = iProver_top
% 2.09/0.99      | v1_pre_topc(k2_tsep_1(X0_42,sK1,sK2)) != iProver_top
% 2.09/0.99      | l1_pre_topc(X0_42) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_862]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5,plain,
% 2.09/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.09/0.99      | ~ m1_pre_topc(X2,X1)
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | v2_struct_0(X2)
% 2.09/0.99      | v1_pre_topc(k2_tsep_1(X1,X0,X2))
% 2.09/0.99      | ~ l1_pre_topc(X1) ),
% 2.09/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_876,plain,
% 2.09/0.99      ( ~ m1_pre_topc(X0_42,X1_42)
% 2.09/0.99      | ~ m1_pre_topc(X2_42,X1_42)
% 2.09/0.99      | v2_struct_0(X1_42)
% 2.09/0.99      | v2_struct_0(X0_42)
% 2.09/0.99      | v2_struct_0(X2_42)
% 2.09/0.99      | v1_pre_topc(k2_tsep_1(X1_42,X0_42,X2_42))
% 2.09/0.99      | ~ l1_pre_topc(X1_42) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1391,plain,
% 2.09/0.99      ( ~ m1_pre_topc(sK2,X0_42)
% 2.09/0.99      | ~ m1_pre_topc(sK1,X0_42)
% 2.09/0.99      | v2_struct_0(X0_42)
% 2.09/0.99      | v2_struct_0(sK2)
% 2.09/0.99      | v2_struct_0(sK1)
% 2.09/0.99      | v1_pre_topc(k2_tsep_1(X0_42,sK1,sK2))
% 2.09/0.99      | ~ l1_pre_topc(X0_42) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_876]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1392,plain,
% 2.09/0.99      ( m1_pre_topc(sK2,X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,X0_42) != iProver_top
% 2.09/0.99      | v2_struct_0(X0_42) = iProver_top
% 2.09/0.99      | v2_struct_0(sK2) = iProver_top
% 2.09/0.99      | v2_struct_0(sK1) = iProver_top
% 2.09/0.99      | v1_pre_topc(k2_tsep_1(X0_42,sK1,sK2)) = iProver_top
% 2.09/0.99      | l1_pre_topc(X0_42) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_1391]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_4,plain,
% 2.09/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.09/0.99      | ~ m1_pre_topc(X2,X1)
% 2.09/0.99      | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | v2_struct_0(X2)
% 2.09/0.99      | ~ l1_pre_topc(X1) ),
% 2.09/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_877,plain,
% 2.09/0.99      ( ~ m1_pre_topc(X0_42,X1_42)
% 2.09/0.99      | ~ m1_pre_topc(X2_42,X1_42)
% 2.09/0.99      | m1_pre_topc(k2_tsep_1(X1_42,X0_42,X2_42),X1_42)
% 2.09/0.99      | v2_struct_0(X1_42)
% 2.09/0.99      | v2_struct_0(X0_42)
% 2.09/0.99      | v2_struct_0(X2_42)
% 2.09/0.99      | ~ l1_pre_topc(X1_42) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1425,plain,
% 2.09/0.99      ( m1_pre_topc(k2_tsep_1(X0_42,sK1,sK2),X0_42)
% 2.09/0.99      | ~ m1_pre_topc(sK2,X0_42)
% 2.09/0.99      | ~ m1_pre_topc(sK1,X0_42)
% 2.09/0.99      | v2_struct_0(X0_42)
% 2.09/0.99      | v2_struct_0(sK2)
% 2.09/0.99      | v2_struct_0(sK1)
% 2.09/0.99      | ~ l1_pre_topc(X0_42) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_877]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1426,plain,
% 2.09/0.99      ( m1_pre_topc(k2_tsep_1(X0_42,sK1,sK2),X0_42) = iProver_top
% 2.09/0.99      | m1_pre_topc(sK2,X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,X0_42) != iProver_top
% 2.09/0.99      | v2_struct_0(X0_42) = iProver_top
% 2.09/0.99      | v2_struct_0(sK2) = iProver_top
% 2.09/0.99      | v2_struct_0(sK1) = iProver_top
% 2.09/0.99      | l1_pre_topc(X0_42) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_1425]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6,plain,
% 2.09/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.09/0.99      | ~ m1_pre_topc(X2,X1)
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | v2_struct_0(X2)
% 2.09/0.99      | ~ v2_struct_0(k2_tsep_1(X1,X0,X2))
% 2.09/0.99      | ~ l1_pre_topc(X1) ),
% 2.09/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_875,plain,
% 2.09/0.99      ( ~ m1_pre_topc(X0_42,X1_42)
% 2.09/0.99      | ~ m1_pre_topc(X2_42,X1_42)
% 2.09/0.99      | v2_struct_0(X1_42)
% 2.09/0.99      | v2_struct_0(X0_42)
% 2.09/0.99      | v2_struct_0(X2_42)
% 2.09/0.99      | ~ v2_struct_0(k2_tsep_1(X1_42,X0_42,X2_42))
% 2.09/0.99      | ~ l1_pre_topc(X1_42) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1462,plain,
% 2.09/0.99      ( ~ m1_pre_topc(sK2,X0_42)
% 2.09/0.99      | ~ m1_pre_topc(sK1,X0_42)
% 2.09/0.99      | v2_struct_0(X0_42)
% 2.09/0.99      | ~ v2_struct_0(k2_tsep_1(X0_42,sK1,sK2))
% 2.09/0.99      | v2_struct_0(sK2)
% 2.09/0.99      | v2_struct_0(sK1)
% 2.09/0.99      | ~ l1_pre_topc(X0_42) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_875]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1463,plain,
% 2.09/0.99      ( m1_pre_topc(sK2,X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,X0_42) != iProver_top
% 2.09/0.99      | v2_struct_0(X0_42) = iProver_top
% 2.09/0.99      | v2_struct_0(k2_tsep_1(X0_42,sK1,sK2)) != iProver_top
% 2.09/0.99      | v2_struct_0(sK2) = iProver_top
% 2.09/0.99      | v2_struct_0(sK1) = iProver_top
% 2.09/0.99      | l1_pre_topc(X0_42) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_1462]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1808,plain,
% 2.09/0.99      ( u1_struct_0(k2_tsep_1(X0_42,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
% 2.09/0.99      | m1_pre_topc(sK2,X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,X0_42) != iProver_top
% 2.09/0.99      | v2_struct_0(X0_42) = iProver_top
% 2.09/0.99      | l1_pre_topc(X0_42) != iProver_top ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_1227,c_26,c_28,c_917,c_1392,c_1426,c_1463]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1819,plain,
% 2.09/0.99      ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2))
% 2.09/0.99      | m1_pre_topc(sK1,sK3) != iProver_top
% 2.09/0.99      | v2_struct_0(sK3) = iProver_top
% 2.09/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1217,c_1808]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_20,negated_conjecture,
% 2.09/0.99      ( l1_pre_topc(sK0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_25,plain,
% 2.09/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_15,negated_conjecture,
% 2.09/0.99      ( ~ v2_struct_0(sK3) ),
% 2.09/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_30,plain,
% 2.09/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_13,negated_conjecture,
% 2.09/0.99      ( m1_pre_topc(sK1,sK3) ),
% 2.09/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_32,plain,
% 2.09/0.99      ( m1_pre_topc(sK1,sK3) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_14,negated_conjecture,
% 2.09/0.99      ( m1_pre_topc(sK3,sK0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_870,negated_conjecture,
% 2.09/0.99      ( m1_pre_topc(sK3,sK0) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1219,plain,
% 2.09/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_870]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1,plain,
% 2.09/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f29]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_878,plain,
% 2.09/0.99      ( ~ m1_pre_topc(X0_42,X1_42)
% 2.09/0.99      | ~ l1_pre_topc(X1_42)
% 2.09/0.99      | l1_pre_topc(X0_42) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1211,plain,
% 2.09/0.99      ( m1_pre_topc(X0_42,X1_42) != iProver_top
% 2.09/0.99      | l1_pre_topc(X1_42) != iProver_top
% 2.09/0.99      | l1_pre_topc(X0_42) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_878]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1510,plain,
% 2.09/0.99      ( l1_pre_topc(sK3) = iProver_top | l1_pre_topc(sK0) != iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1219,c_1211]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1953,plain,
% 2.09/0.99      ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_1819,c_25,c_30,c_32,c_1510]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2,plain,
% 2.09/0.99      ( r1_tsep_1(X0,X1)
% 2.09/0.99      | ~ m1_pre_topc(X0,X2)
% 2.09/0.99      | ~ m1_pre_topc(X3,X2)
% 2.09/0.99      | ~ m1_pre_topc(X1,X2)
% 2.09/0.99      | v2_struct_0(X2)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | v2_struct_0(X3)
% 2.09/0.99      | ~ v1_pre_topc(X3)
% 2.09/0.99      | ~ l1_pre_topc(X2)
% 2.09/0.99      | k2_tsep_1(X2,X0,X1) = X3
% 2.09/0.99      | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) != u1_struct_0(X3) ),
% 2.09/0.99      inference(cnf_transformation,[],[f31]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_272,plain,
% 2.09/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.09/0.99      | ~ m1_pre_topc(X2,X1)
% 2.09/0.99      | ~ m1_pre_topc(X3,X1)
% 2.09/0.99      | v2_struct_0(X3)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | v2_struct_0(X2)
% 2.09/0.99      | ~ v1_pre_topc(X2)
% 2.09/0.99      | ~ l1_pre_topc(X1)
% 2.09/0.99      | k2_tsep_1(X1,X0,X3) = X2
% 2.09/0.99      | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X3)) != u1_struct_0(X2)
% 2.09/0.99      | sK2 != X3
% 2.09/0.99      | sK1 != X0 ),
% 2.09/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_11]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_273,plain,
% 2.09/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.09/0.99      | ~ m1_pre_topc(sK2,X1)
% 2.09/0.99      | ~ m1_pre_topc(sK1,X1)
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | v2_struct_0(sK2)
% 2.09/0.99      | v2_struct_0(sK1)
% 2.09/0.99      | ~ v1_pre_topc(X0)
% 2.09/0.99      | ~ l1_pre_topc(X1)
% 2.09/0.99      | k2_tsep_1(X1,sK1,sK2) = X0
% 2.09/0.99      | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != u1_struct_0(X0) ),
% 2.09/0.99      inference(unflattening,[status(thm)],[c_272]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_277,plain,
% 2.09/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.09/0.99      | ~ m1_pre_topc(sK2,X1)
% 2.09/0.99      | ~ m1_pre_topc(sK1,X1)
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | ~ v1_pre_topc(X0)
% 2.09/0.99      | ~ l1_pre_topc(X1)
% 2.09/0.99      | k2_tsep_1(X1,sK1,sK2) = X0
% 2.09/0.99      | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != u1_struct_0(X0) ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_273,c_19,c_17]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_861,plain,
% 2.09/0.99      ( ~ m1_pre_topc(X0_42,X1_42)
% 2.09/0.99      | ~ m1_pre_topc(sK2,X1_42)
% 2.09/0.99      | ~ m1_pre_topc(sK1,X1_42)
% 2.09/0.99      | v2_struct_0(X1_42)
% 2.09/0.99      | v2_struct_0(X0_42)
% 2.09/0.99      | ~ v1_pre_topc(X0_42)
% 2.09/0.99      | ~ l1_pre_topc(X1_42)
% 2.09/0.99      | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != u1_struct_0(X0_42)
% 2.09/0.99      | k2_tsep_1(X1_42,sK1,sK2) = X0_42 ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_277]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1228,plain,
% 2.09/0.99      ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != u1_struct_0(X0_42)
% 2.09/0.99      | k2_tsep_1(X1_42,sK1,sK2) = X0_42
% 2.09/0.99      | m1_pre_topc(X0_42,X1_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK2,X1_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,X1_42) != iProver_top
% 2.09/0.99      | v2_struct_0(X1_42) = iProver_top
% 2.09/0.99      | v2_struct_0(X0_42) = iProver_top
% 2.09/0.99      | v1_pre_topc(X0_42) != iProver_top
% 2.09/0.99      | l1_pre_topc(X1_42) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_861]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1957,plain,
% 2.09/0.99      ( u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) != u1_struct_0(X0_42)
% 2.09/0.99      | k2_tsep_1(X1_42,sK1,sK2) = X0_42
% 2.09/0.99      | m1_pre_topc(X0_42,X1_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK2,X1_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,X1_42) != iProver_top
% 2.09/0.99      | v2_struct_0(X1_42) = iProver_top
% 2.09/0.99      | v2_struct_0(X0_42) = iProver_top
% 2.09/0.99      | v1_pre_topc(X0_42) != iProver_top
% 2.09/0.99      | l1_pre_topc(X1_42) != iProver_top ),
% 2.09/0.99      inference(demodulation,[status(thm)],[c_1953,c_1228]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_16,negated_conjecture,
% 2.09/0.99      ( m1_pre_topc(sK2,sK0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_868,negated_conjecture,
% 2.09/0.99      ( m1_pre_topc(sK2,sK0) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1221,plain,
% 2.09/0.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_868]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1820,plain,
% 2.09/0.99      ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 2.09/0.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 2.09/0.99      | v2_struct_0(sK0) = iProver_top
% 2.09/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1221,c_1808]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_22,negated_conjecture,
% 2.09/0.99      ( ~ v2_struct_0(sK0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_18,negated_conjecture,
% 2.09/0.99      ( m1_pre_topc(sK1,sK0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_918,plain,
% 2.09/0.99      ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
% 2.09/0.99      | ~ m1_pre_topc(sK2,sK0)
% 2.09/0.99      | ~ m1_pre_topc(sK1,sK0)
% 2.09/0.99      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 2.09/0.99      | v2_struct_0(sK0)
% 2.09/0.99      | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
% 2.09/0.99      | ~ l1_pre_topc(sK0)
% 2.09/0.99      | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_862]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1393,plain,
% 2.09/0.99      ( ~ m1_pre_topc(sK2,sK0)
% 2.09/0.99      | ~ m1_pre_topc(sK1,sK0)
% 2.09/0.99      | v2_struct_0(sK2)
% 2.09/0.99      | v2_struct_0(sK1)
% 2.09/0.99      | v2_struct_0(sK0)
% 2.09/0.99      | v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
% 2.09/0.99      | ~ l1_pre_topc(sK0) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_1391]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1427,plain,
% 2.09/0.99      ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
% 2.09/0.99      | ~ m1_pre_topc(sK2,sK0)
% 2.09/0.99      | ~ m1_pre_topc(sK1,sK0)
% 2.09/0.99      | v2_struct_0(sK2)
% 2.09/0.99      | v2_struct_0(sK1)
% 2.09/0.99      | v2_struct_0(sK0)
% 2.09/0.99      | ~ l1_pre_topc(sK0) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_1425]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1464,plain,
% 2.09/0.99      ( ~ m1_pre_topc(sK2,sK0)
% 2.09/0.99      | ~ m1_pre_topc(sK1,sK0)
% 2.09/0.99      | ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 2.09/0.99      | v2_struct_0(sK2)
% 2.09/0.99      | v2_struct_0(sK1)
% 2.09/0.99      | v2_struct_0(sK0)
% 2.09/0.99      | ~ l1_pre_topc(sK0) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_1462]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_881,plain,( X0_43 = X0_43 ),theory(equality) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1480,plain,
% 2.09/0.99      ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_881]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_883,plain,
% 2.09/0.99      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 2.09/0.99      theory(equality) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1435,plain,
% 2.09/0.99      ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != X0_43
% 2.09/0.99      | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0_42,X1_42,X2_42))
% 2.09/0.99      | u1_struct_0(k2_tsep_1(X0_42,X1_42,X2_42)) != X0_43 ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_883]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1479,plain,
% 2.09/0.99      ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
% 2.09/0.99      | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0_42,X1_42,X2_42))
% 2.09/0.99      | u1_struct_0(k2_tsep_1(X0_42,X1_42,X2_42)) != k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_1435]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1616,plain,
% 2.09/0.99      ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
% 2.09/0.99      | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0_42,sK1,sK2))
% 2.09/0.99      | u1_struct_0(k2_tsep_1(X0_42,sK1,sK2)) != k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_1479]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1617,plain,
% 2.09/0.99      ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
% 2.09/0.99      | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 2.09/0.99      | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) != k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_1616]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2234,plain,
% 2.09/0.99      ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_1820,c_22,c_20,c_19,c_18,c_17,c_16,c_918,c_1393,c_1427,
% 2.09/0.99                 c_1464,c_1480,c_1617]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2237,plain,
% 2.09/0.99      ( u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
% 2.09/0.99      inference(demodulation,[status(thm)],[c_2234,c_1953]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2519,plain,
% 2.09/0.99      ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) != u1_struct_0(X0_42)
% 2.09/0.99      | k2_tsep_1(X1_42,sK1,sK2) = X0_42
% 2.09/0.99      | m1_pre_topc(X0_42,X1_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK2,X1_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,X1_42) != iProver_top
% 2.09/0.99      | v2_struct_0(X1_42) = iProver_top
% 2.09/0.99      | v2_struct_0(X0_42) = iProver_top
% 2.09/0.99      | v1_pre_topc(X0_42) != iProver_top
% 2.09/0.99      | l1_pre_topc(X1_42) != iProver_top ),
% 2.09/0.99      inference(light_normalisation,[status(thm)],[c_1957,c_2237]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2533,plain,
% 2.09/0.99      ( k2_tsep_1(X0_42,sK1,sK2) = k2_tsep_1(sK0,sK1,sK2)
% 2.09/0.99      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK2,X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,X0_42) != iProver_top
% 2.09/0.99      | v2_struct_0(X0_42) = iProver_top
% 2.09/0.99      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) = iProver_top
% 2.09/0.99      | v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) != iProver_top
% 2.09/0.99      | l1_pre_topc(X0_42) != iProver_top ),
% 2.09/0.99      inference(equality_resolution,[status(thm)],[c_2519]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_23,plain,
% 2.09/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_27,plain,
% 2.09/0.99      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_29,plain,
% 2.09/0.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1394,plain,
% 2.09/0.99      ( m1_pre_topc(sK2,sK0) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 2.09/0.99      | v2_struct_0(sK2) = iProver_top
% 2.09/0.99      | v2_struct_0(sK1) = iProver_top
% 2.09/0.99      | v2_struct_0(sK0) = iProver_top
% 2.09/0.99      | v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) = iProver_top
% 2.09/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_1392]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1465,plain,
% 2.09/0.99      ( m1_pre_topc(sK2,sK0) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 2.09/0.99      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) != iProver_top
% 2.09/0.99      | v2_struct_0(sK2) = iProver_top
% 2.09/0.99      | v2_struct_0(sK1) = iProver_top
% 2.09/0.99      | v2_struct_0(sK0) = iProver_top
% 2.09/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_1463]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1386,plain,
% 2.09/0.99      ( ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,X2_42),X3_42)
% 2.09/0.99      | ~ m1_pre_topc(sK2,X3_42)
% 2.09/0.99      | ~ m1_pre_topc(sK1,X3_42)
% 2.09/0.99      | v2_struct_0(X3_42)
% 2.09/0.99      | v2_struct_0(k2_tsep_1(X0_42,X1_42,X2_42))
% 2.09/0.99      | ~ v1_pre_topc(k2_tsep_1(X0_42,X1_42,X2_42))
% 2.09/0.99      | ~ l1_pre_topc(X3_42)
% 2.09/0.99      | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != u1_struct_0(k2_tsep_1(X0_42,X1_42,X2_42))
% 2.09/0.99      | k2_tsep_1(X3_42,sK1,sK2) = k2_tsep_1(X0_42,X1_42,X2_42) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_861]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1629,plain,
% 2.09/0.99      ( ~ m1_pre_topc(k2_tsep_1(X0_42,sK1,sK2),X1_42)
% 2.09/0.99      | ~ m1_pre_topc(sK2,X1_42)
% 2.09/0.99      | ~ m1_pre_topc(sK1,X1_42)
% 2.09/0.99      | v2_struct_0(X1_42)
% 2.09/0.99      | v2_struct_0(k2_tsep_1(X0_42,sK1,sK2))
% 2.09/0.99      | ~ v1_pre_topc(k2_tsep_1(X0_42,sK1,sK2))
% 2.09/0.99      | ~ l1_pre_topc(X1_42)
% 2.09/0.99      | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != u1_struct_0(k2_tsep_1(X0_42,sK1,sK2))
% 2.09/0.99      | k2_tsep_1(X1_42,sK1,sK2) = k2_tsep_1(X0_42,sK1,sK2) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_1386]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2184,plain,
% 2.09/0.99      ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0_42)
% 2.09/0.99      | ~ m1_pre_topc(sK2,X0_42)
% 2.09/0.99      | ~ m1_pre_topc(sK1,X0_42)
% 2.09/0.99      | v2_struct_0(X0_42)
% 2.09/0.99      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 2.09/0.99      | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
% 2.09/0.99      | ~ l1_pre_topc(X0_42)
% 2.09/0.99      | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 2.09/0.99      | k2_tsep_1(X0_42,sK1,sK2) = k2_tsep_1(sK0,sK1,sK2) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_1629]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2185,plain,
% 2.09/0.99      ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) != u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 2.09/0.99      | k2_tsep_1(X0_42,sK1,sK2) = k2_tsep_1(sK0,sK1,sK2)
% 2.09/0.99      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK2,X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,X0_42) != iProver_top
% 2.09/0.99      | v2_struct_0(X0_42) = iProver_top
% 2.09/0.99      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) = iProver_top
% 2.09/0.99      | v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) != iProver_top
% 2.09/0.99      | l1_pre_topc(X0_42) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_2184]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2934,plain,
% 2.09/0.99      ( k2_tsep_1(X0_42,sK1,sK2) = k2_tsep_1(sK0,sK1,sK2)
% 2.09/0.99      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK2,X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,X0_42) != iProver_top
% 2.09/0.99      | v2_struct_0(X0_42) = iProver_top
% 2.09/0.99      | l1_pre_topc(X0_42) != iProver_top ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_2533,c_22,c_23,c_20,c_25,c_19,c_26,c_18,c_27,c_17,c_28,
% 2.09/0.99                 c_16,c_29,c_918,c_1393,c_1394,c_1427,c_1464,c_1465,c_1480,
% 2.09/0.99                 c_1617,c_2185]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2944,plain,
% 2.09/0.99      ( k2_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1,sK2) = k2_tsep_1(sK0,sK1,sK2)
% 2.09/0.99      | m1_pre_topc(sK2,k2_tsep_1(sK0,sK1,sK2)) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,k2_tsep_1(sK0,sK1,sK2)) != iProver_top
% 2.09/0.99      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) = iProver_top
% 2.09/0.99      | l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) != iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1215,c_2934]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_3156,plain,
% 2.09/0.99      ( m1_pre_topc(sK1,k2_tsep_1(sK0,sK1,sK2)) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK2,k2_tsep_1(sK0,sK1,sK2)) != iProver_top
% 2.09/0.99      | k2_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1,sK2) = k2_tsep_1(sK0,sK1,sK2)
% 2.09/0.99      | l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) != iProver_top ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_2944,c_23,c_25,c_26,c_27,c_28,c_29,c_1465]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_3157,plain,
% 2.09/0.99      ( k2_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1,sK2) = k2_tsep_1(sK0,sK1,sK2)
% 2.09/0.99      | m1_pre_topc(sK2,k2_tsep_1(sK0,sK1,sK2)) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,k2_tsep_1(sK0,sK1,sK2)) != iProver_top
% 2.09/0.99      | l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) != iProver_top ),
% 2.09/0.99      inference(renaming,[status(thm)],[c_3156]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2532,plain,
% 2.09/0.99      ( k2_tsep_1(X0_42,sK1,sK2) = k2_tsep_1(sK3,sK1,sK2)
% 2.09/0.99      | m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK2,X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,X0_42) != iProver_top
% 2.09/0.99      | v2_struct_0(X0_42) = iProver_top
% 2.09/0.99      | v2_struct_0(k2_tsep_1(sK3,sK1,sK2)) = iProver_top
% 2.09/0.99      | v1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) != iProver_top
% 2.09/0.99      | l1_pre_topc(X0_42) != iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_2237,c_2519]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_33,plain,
% 2.09/0.99      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1897,plain,
% 2.09/0.99      ( ~ m1_pre_topc(sK2,sK3)
% 2.09/0.99      | ~ m1_pre_topc(sK1,sK3)
% 2.09/0.99      | ~ v2_struct_0(k2_tsep_1(sK3,sK1,sK2))
% 2.09/0.99      | v2_struct_0(sK3)
% 2.09/0.99      | v2_struct_0(sK2)
% 2.09/0.99      | v2_struct_0(sK1)
% 2.09/0.99      | ~ l1_pre_topc(sK3) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_1462]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1898,plain,
% 2.09/0.99      ( m1_pre_topc(sK2,sK3) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,sK3) != iProver_top
% 2.09/0.99      | v2_struct_0(k2_tsep_1(sK3,sK1,sK2)) != iProver_top
% 2.09/0.99      | v2_struct_0(sK3) = iProver_top
% 2.09/0.99      | v2_struct_0(sK2) = iProver_top
% 2.09/0.99      | v2_struct_0(sK1) = iProver_top
% 2.09/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_1897]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2571,plain,
% 2.09/0.99      ( v2_struct_0(X0_42) = iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK2,X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0_42) != iProver_top
% 2.09/0.99      | k2_tsep_1(X0_42,sK1,sK2) = k2_tsep_1(sK3,sK1,sK2)
% 2.09/0.99      | v1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) != iProver_top
% 2.09/0.99      | l1_pre_topc(X0_42) != iProver_top ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_2532,c_25,c_26,c_28,c_30,c_32,c_33,c_1510,c_1898]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2572,plain,
% 2.09/0.99      ( k2_tsep_1(X0_42,sK1,sK2) = k2_tsep_1(sK3,sK1,sK2)
% 2.09/0.99      | m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK2,X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,X0_42) != iProver_top
% 2.09/0.99      | v2_struct_0(X0_42) = iProver_top
% 2.09/0.99      | v1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) != iProver_top
% 2.09/0.99      | l1_pre_topc(X0_42) != iProver_top ),
% 2.09/0.99      inference(renaming,[status(thm)],[c_2571]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2584,plain,
% 2.09/0.99      ( k2_tsep_1(k2_tsep_1(sK3,sK1,sK2),sK1,sK2) = k2_tsep_1(sK3,sK1,sK2)
% 2.09/0.99      | m1_pre_topc(sK2,k2_tsep_1(sK3,sK1,sK2)) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,k2_tsep_1(sK3,sK1,sK2)) != iProver_top
% 2.09/0.99      | v2_struct_0(k2_tsep_1(sK3,sK1,sK2)) = iProver_top
% 2.09/0.99      | v1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) != iProver_top
% 2.09/0.99      | l1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) != iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1215,c_2572]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2924,plain,
% 2.09/0.99      ( m1_pre_topc(sK1,k2_tsep_1(sK3,sK1,sK2)) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK2,k2_tsep_1(sK3,sK1,sK2)) != iProver_top
% 2.09/0.99      | k2_tsep_1(k2_tsep_1(sK3,sK1,sK2),sK1,sK2) = k2_tsep_1(sK3,sK1,sK2)
% 2.09/0.99      | v1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) != iProver_top
% 2.09/0.99      | l1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) != iProver_top ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_2584,c_25,c_26,c_28,c_30,c_32,c_33,c_1510,c_1898]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2925,plain,
% 2.09/0.99      ( k2_tsep_1(k2_tsep_1(sK3,sK1,sK2),sK1,sK2) = k2_tsep_1(sK3,sK1,sK2)
% 2.09/0.99      | m1_pre_topc(sK2,k2_tsep_1(sK3,sK1,sK2)) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,k2_tsep_1(sK3,sK1,sK2)) != iProver_top
% 2.09/0.99      | v1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) != iProver_top
% 2.09/0.99      | l1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) != iProver_top ),
% 2.09/0.99      inference(renaming,[status(thm)],[c_2924]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1956,plain,
% 2.09/0.99      ( u1_struct_0(k2_tsep_1(X0_42,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2))
% 2.09/0.99      | m1_pre_topc(sK2,X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,X0_42) != iProver_top
% 2.09/0.99      | v2_struct_0(X0_42) = iProver_top
% 2.09/0.99      | l1_pre_topc(X0_42) != iProver_top ),
% 2.09/0.99      inference(demodulation,[status(thm)],[c_1953,c_1808]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2324,plain,
% 2.09/0.99      ( u1_struct_0(k2_tsep_1(X0_42,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 2.09/0.99      | m1_pre_topc(sK2,X0_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(sK1,X0_42) != iProver_top
% 2.09/0.99      | v2_struct_0(X0_42) = iProver_top
% 2.09/0.99      | l1_pre_topc(X0_42) != iProver_top ),
% 2.09/0.99      inference(demodulation,[status(thm)],[c_1956,c_2237]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1821,plain,
% 2.09/0.99      ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK2,sK1,sK2))
% 2.09/0.99      | m1_pre_topc(sK1,sK2) != iProver_top
% 2.09/0.99      | v2_struct_0(sK2) = iProver_top
% 2.09/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1215,c_1808]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1508,plain,
% 2.09/0.99      ( l1_pre_topc(sK3) != iProver_top | l1_pre_topc(sK2) = iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1217,c_1211]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2315,plain,
% 2.09/0.99      ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK2,sK1,sK2))
% 2.09/0.99      | m1_pre_topc(sK1,sK2) != iProver_top ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_1821,c_25,c_28,c_1508,c_1510]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2319,plain,
% 2.09/0.99      ( u1_struct_0(k2_tsep_1(sK2,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 2.09/0.99      | m1_pre_topc(sK1,sK2) != iProver_top ),
% 2.09/0.99      inference(light_normalisation,[status(thm)],[c_2315,c_2234]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1212,plain,
% 2.09/0.99      ( m1_pre_topc(X0_42,X1_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(X2_42,X1_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(k2_tsep_1(X1_42,X0_42,X2_42),X1_42) = iProver_top
% 2.09/0.99      | v2_struct_0(X1_42) = iProver_top
% 2.09/0.99      | v2_struct_0(X0_42) = iProver_top
% 2.09/0.99      | v2_struct_0(X2_42) = iProver_top
% 2.09/0.99      | l1_pre_topc(X1_42) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_877]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2000,plain,
% 2.09/0.99      ( m1_pre_topc(X0_42,X1_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(X2_42,X1_42) != iProver_top
% 2.09/0.99      | v2_struct_0(X1_42) = iProver_top
% 2.09/0.99      | v2_struct_0(X0_42) = iProver_top
% 2.09/0.99      | v2_struct_0(X2_42) = iProver_top
% 2.09/0.99      | l1_pre_topc(X1_42) != iProver_top
% 2.09/0.99      | l1_pre_topc(k2_tsep_1(X1_42,X0_42,X2_42)) = iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1212,c_1211]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1730,plain,
% 2.09/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 2.09/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1510,c_25]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_871,negated_conjecture,
% 2.09/0.99      ( m1_pre_topc(sK1,sK3) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1218,plain,
% 2.09/0.99      ( m1_pre_topc(sK1,sK3) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_871]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1509,plain,
% 2.09/0.99      ( l1_pre_topc(sK3) != iProver_top | l1_pre_topc(sK1) = iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1218,c_1211]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1724,plain,
% 2.09/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_1509,c_25,c_1510]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1644,plain,
% 2.09/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_1508,c_25,c_1510]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1214,plain,
% 2.09/0.99      ( m1_pre_topc(X0_42,X1_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(X2_42,X1_42) != iProver_top
% 2.09/0.99      | v2_struct_0(X1_42) = iProver_top
% 2.09/0.99      | v2_struct_0(X0_42) = iProver_top
% 2.09/0.99      | v2_struct_0(X2_42) = iProver_top
% 2.09/0.99      | v2_struct_0(k2_tsep_1(X1_42,X0_42,X2_42)) != iProver_top
% 2.09/0.99      | l1_pre_topc(X1_42) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_875]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1213,plain,
% 2.09/0.99      ( m1_pre_topc(X0_42,X1_42) != iProver_top
% 2.09/0.99      | m1_pre_topc(X2_42,X1_42) != iProver_top
% 2.09/0.99      | v2_struct_0(X1_42) = iProver_top
% 2.09/0.99      | v2_struct_0(X0_42) = iProver_top
% 2.09/0.99      | v2_struct_0(X2_42) = iProver_top
% 2.09/0.99      | v1_pre_topc(k2_tsep_1(X1_42,X0_42,X2_42)) = iProver_top
% 2.09/0.99      | l1_pre_topc(X1_42) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_876]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_10,negated_conjecture,
% 2.09/0.99      ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
% 2.09/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_873,negated_conjecture,
% 2.09/0.99      ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1216,plain,
% 2.09/0.99      ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_873]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_869,negated_conjecture,
% 2.09/0.99      ( ~ v2_struct_0(sK3) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1220,plain,
% 2.09/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_869]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_867,negated_conjecture,
% 2.09/0.99      ( ~ v2_struct_0(sK2) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1222,plain,
% 2.09/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_867]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_866,negated_conjecture,
% 2.09/0.99      ( m1_pre_topc(sK1,sK0) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1223,plain,
% 2.09/0.99      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_866]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_865,negated_conjecture,
% 2.09/0.99      ( ~ v2_struct_0(sK1) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1224,plain,
% 2.09/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_865]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_864,negated_conjecture,
% 2.09/0.99      ( l1_pre_topc(sK0) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1225,plain,
% 2.09/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_864]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_863,negated_conjecture,
% 2.09/0.99      ( ~ v2_struct_0(sK0) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1226,plain,
% 2.09/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_863]) ).
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  % SZS output end Saturation for theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  ------                               Statistics
% 2.09/0.99  
% 2.09/0.99  ------ General
% 2.09/0.99  
% 2.09/0.99  abstr_ref_over_cycles:                  0
% 2.09/0.99  abstr_ref_under_cycles:                 0
% 2.09/0.99  gc_basic_clause_elim:                   0
% 2.09/0.99  forced_gc_time:                         0
% 2.09/0.99  parsing_time:                           0.008
% 2.09/0.99  unif_index_cands_time:                  0.
% 2.09/0.99  unif_index_add_time:                    0.
% 2.09/0.99  orderings_time:                         0.
% 2.09/0.99  out_proof_time:                         0.
% 2.09/0.99  total_time:                             0.115
% 2.09/0.99  num_of_symbols:                         47
% 2.09/0.99  num_of_terms:                           2605
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing
% 2.09/0.99  
% 2.09/0.99  num_of_splits:                          0
% 2.09/0.99  num_of_split_atoms:                     0
% 2.09/0.99  num_of_reused_defs:                     0
% 2.09/0.99  num_eq_ax_congr_red:                    0
% 2.09/0.99  num_of_sem_filtered_clauses:            3
% 2.09/0.99  num_of_subtypes:                        2
% 2.09/0.99  monotx_restored_types:                  0
% 2.09/0.99  sat_num_of_epr_types:                   0
% 2.09/0.99  sat_num_of_non_cyclic_types:            0
% 2.09/0.99  sat_guarded_non_collapsed_types:        1
% 2.09/0.99  num_pure_diseq_elim:                    0
% 2.09/0.99  simp_replaced_by:                       0
% 2.09/0.99  res_preprocessed:                       120
% 2.09/0.99  prep_upred:                             0
% 2.09/0.99  prep_unflattend:                        7
% 2.09/0.99  smt_new_axioms:                         0
% 2.09/0.99  pred_elim_cands:                        4
% 2.09/0.99  pred_elim:                              2
% 2.09/0.99  pred_elim_cl:                           3
% 2.09/0.99  pred_elim_cycles:                       5
% 2.09/0.99  merged_defs:                            0
% 2.09/0.99  merged_defs_ncl:                        0
% 2.09/0.99  bin_hyper_res:                          0
% 2.09/0.99  prep_cycles:                            5
% 2.09/0.99  pred_elim_time:                         0.008
% 2.09/0.99  splitting_time:                         0.
% 2.09/0.99  sem_filter_time:                        0.
% 2.09/0.99  monotx_time:                            0.
% 2.09/0.99  subtype_inf_time:                       0.
% 2.09/0.99  
% 2.09/0.99  ------ Problem properties
% 2.09/0.99  
% 2.09/0.99  clauses:                                18
% 2.09/0.99  conjectures:                            11
% 2.09/0.99  epr:                                    12
% 2.09/0.99  horn:                                   13
% 2.09/0.99  ground:                                 11
% 2.09/0.99  unary:                                  11
% 2.09/0.99  binary:                                 1
% 2.09/0.99  lits:                                   54
% 2.09/0.99  lits_eq:                                3
% 2.09/0.99  fd_pure:                                0
% 2.09/0.99  fd_pseudo:                              0
% 2.09/0.99  fd_cond:                                0
% 2.09/0.99  fd_pseudo_cond:                         1
% 2.09/0.99  ac_symbols:                             0
% 2.09/0.99  
% 2.09/0.99  ------ Propositional Solver
% 2.09/0.99  
% 2.09/0.99  prop_solver_calls:                      32
% 2.09/0.99  prop_fast_solver_calls:                 1052
% 2.09/0.99  smt_solver_calls:                       0
% 2.09/0.99  smt_fast_solver_calls:                  0
% 2.09/0.99  prop_num_of_clauses:                    955
% 2.09/0.99  prop_preprocess_simplified:             3643
% 2.09/0.99  prop_fo_subsumed:                       26
% 2.09/0.99  prop_solver_time:                       0.
% 2.09/0.99  smt_solver_time:                        0.
% 2.09/0.99  smt_fast_solver_time:                   0.
% 2.09/0.99  prop_fast_solver_time:                  0.
% 2.09/0.99  prop_unsat_core_time:                   0.
% 2.09/0.99  
% 2.09/0.99  ------ QBF
% 2.09/0.99  
% 2.09/0.99  qbf_q_res:                              0
% 2.09/0.99  qbf_num_tautologies:                    0
% 2.09/0.99  qbf_prep_cycles:                        0
% 2.09/0.99  
% 2.09/0.99  ------ BMC1
% 2.09/0.99  
% 2.09/0.99  bmc1_current_bound:                     -1
% 2.09/0.99  bmc1_last_solved_bound:                 -1
% 2.09/0.99  bmc1_unsat_core_size:                   -1
% 2.09/0.99  bmc1_unsat_core_parents_size:           -1
% 2.09/0.99  bmc1_merge_next_fun:                    0
% 2.09/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.09/0.99  
% 2.09/0.99  ------ Instantiation
% 2.09/0.99  
% 2.09/0.99  inst_num_of_clauses:                    318
% 2.09/0.99  inst_num_in_passive:                    94
% 2.09/0.99  inst_num_in_active:                     158
% 2.09/0.99  inst_num_in_unprocessed:                66
% 2.09/0.99  inst_num_of_loops:                      170
% 2.09/0.99  inst_num_of_learning_restarts:          0
% 2.09/0.99  inst_num_moves_active_passive:          6
% 2.09/0.99  inst_lit_activity:                      0
% 2.09/0.99  inst_lit_activity_moves:                0
% 2.09/0.99  inst_num_tautologies:                   0
% 2.09/0.99  inst_num_prop_implied:                  0
% 2.09/0.99  inst_num_existing_simplified:           0
% 2.09/0.99  inst_num_eq_res_simplified:             0
% 2.09/0.99  inst_num_child_elim:                    0
% 2.09/0.99  inst_num_of_dismatching_blockings:      103
% 2.09/0.99  inst_num_of_non_proper_insts:           294
% 2.09/0.99  inst_num_of_duplicates:                 0
% 2.09/0.99  inst_inst_num_from_inst_to_res:         0
% 2.09/0.99  inst_dismatching_checking_time:         0.
% 2.09/0.99  
% 2.09/0.99  ------ Resolution
% 2.09/0.99  
% 2.09/0.99  res_num_of_clauses:                     0
% 2.09/0.99  res_num_in_passive:                     0
% 2.09/0.99  res_num_in_active:                      0
% 2.09/0.99  res_num_of_loops:                       125
% 2.09/0.99  res_forward_subset_subsumed:            41
% 2.09/0.99  res_backward_subset_subsumed:           0
% 2.09/0.99  res_forward_subsumed:                   0
% 2.09/0.99  res_backward_subsumed:                  0
% 2.09/0.99  res_forward_subsumption_resolution:     0
% 2.09/0.99  res_backward_subsumption_resolution:    0
% 2.09/0.99  res_clause_to_clause_subsumption:       315
% 2.09/0.99  res_orphan_elimination:                 0
% 2.09/0.99  res_tautology_del:                      30
% 2.09/0.99  res_num_eq_res_simplified:              0
% 2.09/0.99  res_num_sel_changes:                    0
% 2.09/0.99  res_moves_from_active_to_pass:          0
% 2.09/0.99  
% 2.09/0.99  ------ Superposition
% 2.09/0.99  
% 2.09/0.99  sup_time_total:                         0.
% 2.09/0.99  sup_time_generating:                    0.
% 2.09/0.99  sup_time_sim_full:                      0.
% 2.09/0.99  sup_time_sim_immed:                     0.
% 2.09/0.99  
% 2.09/0.99  sup_num_of_clauses:                     30
% 2.09/0.99  sup_num_in_active:                      29
% 2.09/0.99  sup_num_in_passive:                     1
% 2.09/0.99  sup_num_of_loops:                       32
% 2.09/0.99  sup_fw_superposition:                   16
% 2.09/0.99  sup_bw_superposition:                   2
% 2.09/0.99  sup_immediate_simplified:               2
% 2.09/0.99  sup_given_eliminated:                   0
% 2.09/0.99  comparisons_done:                       0
% 2.09/0.99  comparisons_avoided:                    0
% 2.09/0.99  
% 2.09/0.99  ------ Simplifications
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  sim_fw_subset_subsumed:                 2
% 2.09/0.99  sim_bw_subset_subsumed:                 2
% 2.09/0.99  sim_fw_subsumed:                        0
% 2.09/0.99  sim_bw_subsumed:                        0
% 2.09/0.99  sim_fw_subsumption_res:                 0
% 2.09/0.99  sim_bw_subsumption_res:                 0
% 2.09/0.99  sim_tautology_del:                      1
% 2.09/0.99  sim_eq_tautology_del:                   3
% 2.09/0.99  sim_eq_res_simp:                        0
% 2.09/0.99  sim_fw_demodulated:                     1
% 2.09/0.99  sim_bw_demodulated:                     3
% 2.09/0.99  sim_light_normalised:                   2
% 2.09/0.99  sim_joinable_taut:                      0
% 2.09/0.99  sim_joinable_simp:                      0
% 2.09/0.99  sim_ac_normalised:                      0
% 2.09/0.99  sim_smt_subsumption:                    0
% 2.09/0.99  
%------------------------------------------------------------------------------
