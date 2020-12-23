%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:08 EST 2020

% Result     : Theorem 7.51s
% Output     : CNFRefutation 7.51s
% Verified   : 
% Statistics : Number of formulae       :  194 (1354 expanded)
%              Number of clauses        :  133 ( 334 expanded)
%              Number of leaves         :   16 ( 475 expanded)
%              Depth                    :   20
%              Number of atoms          :  870 (13298 expanded)
%              Number of equality atoms :  220 ( 439 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,
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

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f37,f36,f35,f34])).

fof(f58,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
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
                  <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3) )
                    & ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)
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
    inference(nnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)
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
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f6,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

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

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
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
             => ( m1_pre_topc(X1,X2)
              <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) )
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
              ( ( m1_pre_topc(X1,X2)
              <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X2)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_tsep_1(X0,X1,X2) )
                & ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)
                  | ~ m1_pre_topc(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f50,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f65,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_716,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1220,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_720,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1216,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_720])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v1_pre_topc(k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_150,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_8,c_7,c_6])).

cnf(c_151,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(renaming,[status(thm)],[c_150])).

cnf(c_712,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X2_43)
    | ~ l1_pre_topc(X1_43)
    | u1_struct_0(k1_tsep_1(X1_43,X0_43,X2_43)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X2_43)) ),
    inference(subtyping,[status(esa)],[c_151])).

cnf(c_1224,plain,
    ( u1_struct_0(k1_tsep_1(X0_43,X1_43,X2_43)) = k2_xboole_0(u1_struct_0(X1_43),u1_struct_0(X2_43))
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | m1_pre_topc(X2_43,X0_43) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_712])).

cnf(c_4414,plain,
    ( u1_struct_0(k1_tsep_1(sK0,X0_43,sK3)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_1224])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_27,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_29,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_34,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5450,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | u1_struct_0(k1_tsep_1(sK0,X0_43,sK3)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4414,c_27,c_29,c_34])).

cnf(c_5451,plain,
    ( u1_struct_0(k1_tsep_1(sK0,X0_43,sK3)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_5450])).

cnf(c_5461,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1220,c_5451])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_721,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1215,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_721])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_722,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1214,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_722])).

cnf(c_4412,plain,
    ( u1_struct_0(k1_tsep_1(sK2,X0_43,sK3)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3))
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1214,c_1224])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_32,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_33,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_731,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ l1_pre_topc(X1_43)
    | l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1540,plain,
    ( ~ m1_pre_topc(sK2,X0_43)
    | ~ l1_pre_topc(X0_43)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_1541,plain,
    ( m1_pre_topc(sK2,X0_43) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1540])).

cnf(c_1543,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1541])).

cnf(c_5034,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | u1_struct_0(k1_tsep_1(sK2,X0_43,sK3)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4412,c_29,c_32,c_33,c_34,c_1543])).

cnf(c_5035,plain,
    ( u1_struct_0(k1_tsep_1(sK2,X0_43,sK3)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3))
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_5034])).

cnf(c_5044,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1215,c_5035])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_30,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5147,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5044,c_30])).

cnf(c_5488,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5461,c_5147])).

cnf(c_14609,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5488,c_30])).

cnf(c_14618,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(demodulation,[status(thm)],[c_14609,c_5147])).

cnf(c_718,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1218,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_5460,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_5451])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | k1_tsep_1(X1,X2,X0) = k1_tsep_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_729,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X2_43)
    | ~ l1_pre_topc(X1_43)
    | k1_tsep_1(X1_43,X2_43,X0_43) = k1_tsep_1(X1_43,X0_43,X2_43) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1207,plain,
    ( k1_tsep_1(X0_43,X1_43,X2_43) = k1_tsep_1(X0_43,X2_43,X1_43)
    | m1_pre_topc(X2_43,X0_43) != iProver_top
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_3187,plain,
    ( k1_tsep_1(sK0,sK3,X0_43) = k1_tsep_1(sK0,X0_43,sK3)
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_1207])).

cnf(c_4039,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | k1_tsep_1(sK0,sK3,X0_43) = k1_tsep_1(sK0,X0_43,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3187,c_27,c_29,c_34])).

cnf(c_4040,plain,
    ( k1_tsep_1(sK0,sK3,X0_43) = k1_tsep_1(sK0,X0_43,sK3)
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_4039])).

cnf(c_4049,plain,
    ( k1_tsep_1(sK0,sK2,sK3) = k1_tsep_1(sK0,sK3,sK2)
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_4040])).

cnf(c_4168,plain,
    ( k1_tsep_1(sK0,sK2,sK3) = k1_tsep_1(sK0,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4049,c_32])).

cnf(c_5493,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK3,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | v2_struct_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5460,c_4168])).

cnf(c_18881,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK3,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5493,c_32])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_405,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X1,X0,X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_406,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X0,X1) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_408,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_406,c_26,c_24])).

cnf(c_409,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X0,X1) ),
    inference(renaming,[status(thm)],[c_408])).

cnf(c_708,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(X1_43)
    | g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43)) = k1_tsep_1(sK0,X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_409])).

cnf(c_1228,plain,
    ( g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(sK0,X1_43,X0_43)
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(c_2731,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK3,sK2)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1214,c_1228])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_384,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_385,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_389,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_385,c_26,c_24])).

cnf(c_709,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | v2_struct_0(X0_43)
    | g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(sK0,X0_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_389])).

cnf(c_1227,plain,
    ( g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(sK0,X0_43,X0_43)
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_709])).

cnf(c_2113,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_1227])).

cnf(c_1783,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_2569,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2113,c_21,c_20,c_1783])).

cnf(c_2804,plain,
    ( k1_tsep_1(sK0,sK3,sK2) = k1_tsep_1(sK0,sK2,sK2)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2731,c_2569])).

cnf(c_35,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15891,plain,
    ( k1_tsep_1(sK0,sK3,sK2) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2804,c_32,c_33,c_34,c_35])).

cnf(c_2732,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1215,c_1228])).

cnf(c_2793,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK2)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2732,c_2569])).

cnf(c_31,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_14891,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2793,c_30,c_31,c_32,c_33])).

cnf(c_15893,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_15891,c_14891])).

cnf(c_18883,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(light_normalisation,[status(thm)],[c_18881,c_15893])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_732,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | r1_tarski(k2_xboole_0(X0_44,X2_44),k2_xboole_0(X1_44,X2_44)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1204,plain,
    ( r1_tarski(X0_44,X1_44) != iProver_top
    | r1_tarski(k2_xboole_0(X0_44,X2_44),k2_xboole_0(X1_44,X2_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_18886,plain,
    ( r1_tarski(X0_44,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k2_xboole_0(X0_44,u1_struct_0(sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_18883,c_1204])).

cnf(c_19310,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) = iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14618,c_18886])).

cnf(c_727,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | m1_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43),X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X2_43)
    | ~ l1_pre_topc(X1_43) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_4805,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_727])).

cnf(c_4808,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4805])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_340,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_341,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_343,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_341,c_24])).

cnf(c_344,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_343])).

cnf(c_711,plain,
    ( m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
    inference(subtyping,[status(esa)],[c_344])).

cnf(c_3877,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_3878,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) != iProver_top
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3877])).

cnf(c_742,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | m1_pre_topc(X2_43,X3_43)
    | X2_43 != X0_43
    | X3_43 != X1_43 ),
    theory(equality)).

cnf(c_1639,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | k1_tsep_1(sK0,sK1,sK3) != X0_43
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X1_43 ),
    inference(instantiation,[status(thm)],[c_742])).

cnf(c_1762,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_43)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | k1_tsep_1(sK0,sK1,sK3) != k1_tsep_1(sK0,sK1,sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0_43 ),
    inference(instantiation,[status(thm)],[c_1639])).

cnf(c_2298,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2))
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | k1_tsep_1(sK0,sK1,sK3) != k1_tsep_1(sK0,sK1,sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1762])).

cnf(c_2302,plain,
    ( k1_tsep_1(sK0,sK1,sK3) != k1_tsep_1(sK0,sK1,sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK1,sK2)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2298])).

cnf(c_1777,plain,
    ( ~ m1_pre_topc(X0_43,sK2)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,X0_43,sK2) ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_2079,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1777])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_360,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_361,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_365,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_361,c_24])).

cnf(c_366,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_365])).

cnf(c_710,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
    inference(subtyping,[status(esa)],[c_366])).

cnf(c_1749,plain,
    ( ~ m1_pre_topc(X0_43,sK2)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tarski(u1_struct_0(X0_43),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_2048,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1749])).

cnf(c_2049,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK2) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2048])).

cnf(c_734,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_1763,plain,
    ( k1_tsep_1(sK0,sK1,sK3) = k1_tsep_1(sK0,sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_1522,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_727])).

cnf(c_1523,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1522])).

cnf(c_2,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_730,plain,
    ( m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43)))
    | ~ l1_pre_topc(X1_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1481,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_730])).

cnf(c_1482,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1481])).

cnf(c_15,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_38,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_36,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19310,c_4808,c_3878,c_2302,c_2079,c_2049,c_1763,c_1543,c_1523,c_1482,c_38,c_36,c_17,c_35,c_34,c_33,c_20,c_32,c_21,c_31,c_22,c_30,c_23,c_29,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:57:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.51/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/1.49  
% 7.51/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.51/1.49  
% 7.51/1.49  ------  iProver source info
% 7.51/1.49  
% 7.51/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.51/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.51/1.49  git: non_committed_changes: false
% 7.51/1.49  git: last_make_outside_of_git: false
% 7.51/1.49  
% 7.51/1.49  ------ 
% 7.51/1.49  
% 7.51/1.49  ------ Input Options
% 7.51/1.49  
% 7.51/1.49  --out_options                           all
% 7.51/1.49  --tptp_safe_out                         true
% 7.51/1.49  --problem_path                          ""
% 7.51/1.49  --include_path                          ""
% 7.51/1.49  --clausifier                            res/vclausify_rel
% 7.51/1.49  --clausifier_options                    --mode clausify
% 7.51/1.49  --stdin                                 false
% 7.51/1.49  --stats_out                             all
% 7.51/1.49  
% 7.51/1.49  ------ General Options
% 7.51/1.49  
% 7.51/1.49  --fof                                   false
% 7.51/1.49  --time_out_real                         305.
% 7.51/1.49  --time_out_virtual                      -1.
% 7.51/1.49  --symbol_type_check                     false
% 7.51/1.49  --clausify_out                          false
% 7.51/1.49  --sig_cnt_out                           false
% 7.51/1.49  --trig_cnt_out                          false
% 7.51/1.49  --trig_cnt_out_tolerance                1.
% 7.51/1.49  --trig_cnt_out_sk_spl                   false
% 7.51/1.49  --abstr_cl_out                          false
% 7.51/1.49  
% 7.51/1.49  ------ Global Options
% 7.51/1.49  
% 7.51/1.49  --schedule                              default
% 7.51/1.49  --add_important_lit                     false
% 7.51/1.49  --prop_solver_per_cl                    1000
% 7.51/1.49  --min_unsat_core                        false
% 7.51/1.49  --soft_assumptions                      false
% 7.51/1.49  --soft_lemma_size                       3
% 7.51/1.49  --prop_impl_unit_size                   0
% 7.51/1.49  --prop_impl_unit                        []
% 7.51/1.49  --share_sel_clauses                     true
% 7.51/1.49  --reset_solvers                         false
% 7.51/1.49  --bc_imp_inh                            [conj_cone]
% 7.51/1.49  --conj_cone_tolerance                   3.
% 7.51/1.49  --extra_neg_conj                        none
% 7.51/1.49  --large_theory_mode                     true
% 7.51/1.49  --prolific_symb_bound                   200
% 7.51/1.49  --lt_threshold                          2000
% 7.51/1.49  --clause_weak_htbl                      true
% 7.51/1.49  --gc_record_bc_elim                     false
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing Options
% 7.51/1.49  
% 7.51/1.49  --preprocessing_flag                    true
% 7.51/1.49  --time_out_prep_mult                    0.1
% 7.51/1.49  --splitting_mode                        input
% 7.51/1.49  --splitting_grd                         true
% 7.51/1.49  --splitting_cvd                         false
% 7.51/1.49  --splitting_cvd_svl                     false
% 7.51/1.49  --splitting_nvd                         32
% 7.51/1.49  --sub_typing                            true
% 7.51/1.49  --prep_gs_sim                           true
% 7.51/1.49  --prep_unflatten                        true
% 7.51/1.49  --prep_res_sim                          true
% 7.51/1.49  --prep_upred                            true
% 7.51/1.49  --prep_sem_filter                       exhaustive
% 7.51/1.49  --prep_sem_filter_out                   false
% 7.51/1.49  --pred_elim                             true
% 7.51/1.49  --res_sim_input                         true
% 7.51/1.49  --eq_ax_congr_red                       true
% 7.51/1.49  --pure_diseq_elim                       true
% 7.51/1.49  --brand_transform                       false
% 7.51/1.49  --non_eq_to_eq                          false
% 7.51/1.49  --prep_def_merge                        true
% 7.51/1.49  --prep_def_merge_prop_impl              false
% 7.51/1.49  --prep_def_merge_mbd                    true
% 7.51/1.49  --prep_def_merge_tr_red                 false
% 7.51/1.49  --prep_def_merge_tr_cl                  false
% 7.51/1.49  --smt_preprocessing                     true
% 7.51/1.49  --smt_ac_axioms                         fast
% 7.51/1.49  --preprocessed_out                      false
% 7.51/1.49  --preprocessed_stats                    false
% 7.51/1.49  
% 7.51/1.49  ------ Abstraction refinement Options
% 7.51/1.49  
% 7.51/1.49  --abstr_ref                             []
% 7.51/1.49  --abstr_ref_prep                        false
% 7.51/1.49  --abstr_ref_until_sat                   false
% 7.51/1.49  --abstr_ref_sig_restrict                funpre
% 7.51/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.51/1.49  --abstr_ref_under                       []
% 7.51/1.49  
% 7.51/1.49  ------ SAT Options
% 7.51/1.49  
% 7.51/1.49  --sat_mode                              false
% 7.51/1.49  --sat_fm_restart_options                ""
% 7.51/1.49  --sat_gr_def                            false
% 7.51/1.49  --sat_epr_types                         true
% 7.51/1.49  --sat_non_cyclic_types                  false
% 7.51/1.49  --sat_finite_models                     false
% 7.51/1.49  --sat_fm_lemmas                         false
% 7.51/1.49  --sat_fm_prep                           false
% 7.51/1.49  --sat_fm_uc_incr                        true
% 7.51/1.49  --sat_out_model                         small
% 7.51/1.49  --sat_out_clauses                       false
% 7.51/1.49  
% 7.51/1.49  ------ QBF Options
% 7.51/1.49  
% 7.51/1.49  --qbf_mode                              false
% 7.51/1.49  --qbf_elim_univ                         false
% 7.51/1.49  --qbf_dom_inst                          none
% 7.51/1.49  --qbf_dom_pre_inst                      false
% 7.51/1.49  --qbf_sk_in                             false
% 7.51/1.49  --qbf_pred_elim                         true
% 7.51/1.49  --qbf_split                             512
% 7.51/1.49  
% 7.51/1.49  ------ BMC1 Options
% 7.51/1.49  
% 7.51/1.49  --bmc1_incremental                      false
% 7.51/1.49  --bmc1_axioms                           reachable_all
% 7.51/1.49  --bmc1_min_bound                        0
% 7.51/1.49  --bmc1_max_bound                        -1
% 7.51/1.49  --bmc1_max_bound_default                -1
% 7.51/1.49  --bmc1_symbol_reachability              true
% 7.51/1.49  --bmc1_property_lemmas                  false
% 7.51/1.49  --bmc1_k_induction                      false
% 7.51/1.49  --bmc1_non_equiv_states                 false
% 7.51/1.49  --bmc1_deadlock                         false
% 7.51/1.49  --bmc1_ucm                              false
% 7.51/1.49  --bmc1_add_unsat_core                   none
% 7.51/1.49  --bmc1_unsat_core_children              false
% 7.51/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.51/1.49  --bmc1_out_stat                         full
% 7.51/1.49  --bmc1_ground_init                      false
% 7.51/1.49  --bmc1_pre_inst_next_state              false
% 7.51/1.49  --bmc1_pre_inst_state                   false
% 7.51/1.49  --bmc1_pre_inst_reach_state             false
% 7.51/1.49  --bmc1_out_unsat_core                   false
% 7.51/1.49  --bmc1_aig_witness_out                  false
% 7.51/1.49  --bmc1_verbose                          false
% 7.51/1.49  --bmc1_dump_clauses_tptp                false
% 7.51/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.51/1.49  --bmc1_dump_file                        -
% 7.51/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.51/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.51/1.49  --bmc1_ucm_extend_mode                  1
% 7.51/1.49  --bmc1_ucm_init_mode                    2
% 7.51/1.49  --bmc1_ucm_cone_mode                    none
% 7.51/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.51/1.49  --bmc1_ucm_relax_model                  4
% 7.51/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.51/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.51/1.49  --bmc1_ucm_layered_model                none
% 7.51/1.49  --bmc1_ucm_max_lemma_size               10
% 7.51/1.49  
% 7.51/1.49  ------ AIG Options
% 7.51/1.49  
% 7.51/1.49  --aig_mode                              false
% 7.51/1.49  
% 7.51/1.49  ------ Instantiation Options
% 7.51/1.49  
% 7.51/1.49  --instantiation_flag                    true
% 7.51/1.49  --inst_sos_flag                         false
% 7.51/1.49  --inst_sos_phase                        true
% 7.51/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.51/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.51/1.49  --inst_lit_sel_side                     num_symb
% 7.51/1.49  --inst_solver_per_active                1400
% 7.51/1.49  --inst_solver_calls_frac                1.
% 7.51/1.49  --inst_passive_queue_type               priority_queues
% 7.51/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.51/1.49  --inst_passive_queues_freq              [25;2]
% 7.51/1.49  --inst_dismatching                      true
% 7.51/1.49  --inst_eager_unprocessed_to_passive     true
% 7.51/1.49  --inst_prop_sim_given                   true
% 7.51/1.49  --inst_prop_sim_new                     false
% 7.51/1.49  --inst_subs_new                         false
% 7.51/1.49  --inst_eq_res_simp                      false
% 7.51/1.49  --inst_subs_given                       false
% 7.51/1.49  --inst_orphan_elimination               true
% 7.51/1.49  --inst_learning_loop_flag               true
% 7.51/1.49  --inst_learning_start                   3000
% 7.51/1.49  --inst_learning_factor                  2
% 7.51/1.49  --inst_start_prop_sim_after_learn       3
% 7.51/1.49  --inst_sel_renew                        solver
% 7.51/1.49  --inst_lit_activity_flag                true
% 7.51/1.49  --inst_restr_to_given                   false
% 7.51/1.49  --inst_activity_threshold               500
% 7.51/1.49  --inst_out_proof                        true
% 7.51/1.49  
% 7.51/1.49  ------ Resolution Options
% 7.51/1.49  
% 7.51/1.49  --resolution_flag                       true
% 7.51/1.49  --res_lit_sel                           adaptive
% 7.51/1.49  --res_lit_sel_side                      none
% 7.51/1.49  --res_ordering                          kbo
% 7.51/1.49  --res_to_prop_solver                    active
% 7.51/1.49  --res_prop_simpl_new                    false
% 7.51/1.49  --res_prop_simpl_given                  true
% 7.51/1.49  --res_passive_queue_type                priority_queues
% 7.51/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.51/1.49  --res_passive_queues_freq               [15;5]
% 7.51/1.49  --res_forward_subs                      full
% 7.51/1.49  --res_backward_subs                     full
% 7.51/1.49  --res_forward_subs_resolution           true
% 7.51/1.49  --res_backward_subs_resolution          true
% 7.51/1.49  --res_orphan_elimination                true
% 7.51/1.49  --res_time_limit                        2.
% 7.51/1.49  --res_out_proof                         true
% 7.51/1.49  
% 7.51/1.49  ------ Superposition Options
% 7.51/1.49  
% 7.51/1.49  --superposition_flag                    true
% 7.51/1.49  --sup_passive_queue_type                priority_queues
% 7.51/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.51/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.51/1.49  --demod_completeness_check              fast
% 7.51/1.49  --demod_use_ground                      true
% 7.51/1.49  --sup_to_prop_solver                    passive
% 7.51/1.49  --sup_prop_simpl_new                    true
% 7.51/1.49  --sup_prop_simpl_given                  true
% 7.51/1.49  --sup_fun_splitting                     false
% 7.51/1.49  --sup_smt_interval                      50000
% 7.51/1.49  
% 7.51/1.49  ------ Superposition Simplification Setup
% 7.51/1.49  
% 7.51/1.49  --sup_indices_passive                   []
% 7.51/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.51/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.51/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.51/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.51/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.51/1.49  --sup_full_bw                           [BwDemod]
% 7.51/1.49  --sup_immed_triv                        [TrivRules]
% 7.51/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.51/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.51/1.49  --sup_immed_bw_main                     []
% 7.51/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.51/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.51/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.51/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.51/1.49  
% 7.51/1.49  ------ Combination Options
% 7.51/1.49  
% 7.51/1.49  --comb_res_mult                         3
% 7.51/1.49  --comb_sup_mult                         2
% 7.51/1.49  --comb_inst_mult                        10
% 7.51/1.49  
% 7.51/1.49  ------ Debug Options
% 7.51/1.49  
% 7.51/1.49  --dbg_backtrace                         false
% 7.51/1.49  --dbg_dump_prop_clauses                 false
% 7.51/1.49  --dbg_dump_prop_clauses_file            -
% 7.51/1.49  --dbg_out_stat                          false
% 7.51/1.49  ------ Parsing...
% 7.51/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.51/1.49  ------ Proving...
% 7.51/1.49  ------ Problem Properties 
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  clauses                                 26
% 7.51/1.49  conjectures                             11
% 7.51/1.49  EPR                                     12
% 7.51/1.49  Horn                                    17
% 7.51/1.49  unary                                   11
% 7.51/1.49  binary                                  2
% 7.51/1.49  lits                                    90
% 7.51/1.49  lits eq                                 7
% 7.51/1.49  fd_pure                                 0
% 7.51/1.49  fd_pseudo                               0
% 7.51/1.49  fd_cond                                 0
% 7.51/1.49  fd_pseudo_cond                          1
% 7.51/1.49  AC symbols                              0
% 7.51/1.49  
% 7.51/1.49  ------ Schedule dynamic 5 is on 
% 7.51/1.49  
% 7.51/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  ------ 
% 7.51/1.49  Current options:
% 7.51/1.49  ------ 
% 7.51/1.49  
% 7.51/1.49  ------ Input Options
% 7.51/1.49  
% 7.51/1.49  --out_options                           all
% 7.51/1.49  --tptp_safe_out                         true
% 7.51/1.49  --problem_path                          ""
% 7.51/1.49  --include_path                          ""
% 7.51/1.49  --clausifier                            res/vclausify_rel
% 7.51/1.49  --clausifier_options                    --mode clausify
% 7.51/1.49  --stdin                                 false
% 7.51/1.49  --stats_out                             all
% 7.51/1.49  
% 7.51/1.49  ------ General Options
% 7.51/1.49  
% 7.51/1.49  --fof                                   false
% 7.51/1.49  --time_out_real                         305.
% 7.51/1.49  --time_out_virtual                      -1.
% 7.51/1.49  --symbol_type_check                     false
% 7.51/1.49  --clausify_out                          false
% 7.51/1.49  --sig_cnt_out                           false
% 7.51/1.49  --trig_cnt_out                          false
% 7.51/1.49  --trig_cnt_out_tolerance                1.
% 7.51/1.49  --trig_cnt_out_sk_spl                   false
% 7.51/1.49  --abstr_cl_out                          false
% 7.51/1.49  
% 7.51/1.49  ------ Global Options
% 7.51/1.49  
% 7.51/1.49  --schedule                              default
% 7.51/1.49  --add_important_lit                     false
% 7.51/1.49  --prop_solver_per_cl                    1000
% 7.51/1.49  --min_unsat_core                        false
% 7.51/1.49  --soft_assumptions                      false
% 7.51/1.49  --soft_lemma_size                       3
% 7.51/1.49  --prop_impl_unit_size                   0
% 7.51/1.49  --prop_impl_unit                        []
% 7.51/1.49  --share_sel_clauses                     true
% 7.51/1.49  --reset_solvers                         false
% 7.51/1.49  --bc_imp_inh                            [conj_cone]
% 7.51/1.49  --conj_cone_tolerance                   3.
% 7.51/1.49  --extra_neg_conj                        none
% 7.51/1.49  --large_theory_mode                     true
% 7.51/1.49  --prolific_symb_bound                   200
% 7.51/1.49  --lt_threshold                          2000
% 7.51/1.49  --clause_weak_htbl                      true
% 7.51/1.49  --gc_record_bc_elim                     false
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing Options
% 7.51/1.49  
% 7.51/1.49  --preprocessing_flag                    true
% 7.51/1.49  --time_out_prep_mult                    0.1
% 7.51/1.49  --splitting_mode                        input
% 7.51/1.49  --splitting_grd                         true
% 7.51/1.49  --splitting_cvd                         false
% 7.51/1.49  --splitting_cvd_svl                     false
% 7.51/1.49  --splitting_nvd                         32
% 7.51/1.49  --sub_typing                            true
% 7.51/1.49  --prep_gs_sim                           true
% 7.51/1.49  --prep_unflatten                        true
% 7.51/1.49  --prep_res_sim                          true
% 7.51/1.49  --prep_upred                            true
% 7.51/1.49  --prep_sem_filter                       exhaustive
% 7.51/1.49  --prep_sem_filter_out                   false
% 7.51/1.49  --pred_elim                             true
% 7.51/1.49  --res_sim_input                         true
% 7.51/1.49  --eq_ax_congr_red                       true
% 7.51/1.49  --pure_diseq_elim                       true
% 7.51/1.49  --brand_transform                       false
% 7.51/1.49  --non_eq_to_eq                          false
% 7.51/1.49  --prep_def_merge                        true
% 7.51/1.49  --prep_def_merge_prop_impl              false
% 7.51/1.49  --prep_def_merge_mbd                    true
% 7.51/1.49  --prep_def_merge_tr_red                 false
% 7.51/1.49  --prep_def_merge_tr_cl                  false
% 7.51/1.49  --smt_preprocessing                     true
% 7.51/1.49  --smt_ac_axioms                         fast
% 7.51/1.49  --preprocessed_out                      false
% 7.51/1.49  --preprocessed_stats                    false
% 7.51/1.49  
% 7.51/1.49  ------ Abstraction refinement Options
% 7.51/1.49  
% 7.51/1.49  --abstr_ref                             []
% 7.51/1.49  --abstr_ref_prep                        false
% 7.51/1.49  --abstr_ref_until_sat                   false
% 7.51/1.49  --abstr_ref_sig_restrict                funpre
% 7.51/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.51/1.49  --abstr_ref_under                       []
% 7.51/1.49  
% 7.51/1.49  ------ SAT Options
% 7.51/1.49  
% 7.51/1.49  --sat_mode                              false
% 7.51/1.49  --sat_fm_restart_options                ""
% 7.51/1.49  --sat_gr_def                            false
% 7.51/1.49  --sat_epr_types                         true
% 7.51/1.49  --sat_non_cyclic_types                  false
% 7.51/1.49  --sat_finite_models                     false
% 7.51/1.49  --sat_fm_lemmas                         false
% 7.51/1.49  --sat_fm_prep                           false
% 7.51/1.49  --sat_fm_uc_incr                        true
% 7.51/1.49  --sat_out_model                         small
% 7.51/1.49  --sat_out_clauses                       false
% 7.51/1.49  
% 7.51/1.49  ------ QBF Options
% 7.51/1.49  
% 7.51/1.49  --qbf_mode                              false
% 7.51/1.49  --qbf_elim_univ                         false
% 7.51/1.49  --qbf_dom_inst                          none
% 7.51/1.49  --qbf_dom_pre_inst                      false
% 7.51/1.49  --qbf_sk_in                             false
% 7.51/1.49  --qbf_pred_elim                         true
% 7.51/1.49  --qbf_split                             512
% 7.51/1.49  
% 7.51/1.49  ------ BMC1 Options
% 7.51/1.49  
% 7.51/1.49  --bmc1_incremental                      false
% 7.51/1.49  --bmc1_axioms                           reachable_all
% 7.51/1.49  --bmc1_min_bound                        0
% 7.51/1.49  --bmc1_max_bound                        -1
% 7.51/1.49  --bmc1_max_bound_default                -1
% 7.51/1.49  --bmc1_symbol_reachability              true
% 7.51/1.49  --bmc1_property_lemmas                  false
% 7.51/1.49  --bmc1_k_induction                      false
% 7.51/1.49  --bmc1_non_equiv_states                 false
% 7.51/1.49  --bmc1_deadlock                         false
% 7.51/1.49  --bmc1_ucm                              false
% 7.51/1.49  --bmc1_add_unsat_core                   none
% 7.51/1.49  --bmc1_unsat_core_children              false
% 7.51/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.51/1.49  --bmc1_out_stat                         full
% 7.51/1.49  --bmc1_ground_init                      false
% 7.51/1.49  --bmc1_pre_inst_next_state              false
% 7.51/1.49  --bmc1_pre_inst_state                   false
% 7.51/1.49  --bmc1_pre_inst_reach_state             false
% 7.51/1.49  --bmc1_out_unsat_core                   false
% 7.51/1.49  --bmc1_aig_witness_out                  false
% 7.51/1.49  --bmc1_verbose                          false
% 7.51/1.49  --bmc1_dump_clauses_tptp                false
% 7.51/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.51/1.49  --bmc1_dump_file                        -
% 7.51/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.51/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.51/1.49  --bmc1_ucm_extend_mode                  1
% 7.51/1.49  --bmc1_ucm_init_mode                    2
% 7.51/1.49  --bmc1_ucm_cone_mode                    none
% 7.51/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.51/1.49  --bmc1_ucm_relax_model                  4
% 7.51/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.51/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.51/1.49  --bmc1_ucm_layered_model                none
% 7.51/1.49  --bmc1_ucm_max_lemma_size               10
% 7.51/1.49  
% 7.51/1.49  ------ AIG Options
% 7.51/1.49  
% 7.51/1.49  --aig_mode                              false
% 7.51/1.49  
% 7.51/1.49  ------ Instantiation Options
% 7.51/1.49  
% 7.51/1.49  --instantiation_flag                    true
% 7.51/1.49  --inst_sos_flag                         false
% 7.51/1.49  --inst_sos_phase                        true
% 7.51/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.51/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.51/1.49  --inst_lit_sel_side                     none
% 7.51/1.49  --inst_solver_per_active                1400
% 7.51/1.49  --inst_solver_calls_frac                1.
% 7.51/1.49  --inst_passive_queue_type               priority_queues
% 7.51/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.51/1.49  --inst_passive_queues_freq              [25;2]
% 7.51/1.49  --inst_dismatching                      true
% 7.51/1.49  --inst_eager_unprocessed_to_passive     true
% 7.51/1.49  --inst_prop_sim_given                   true
% 7.51/1.49  --inst_prop_sim_new                     false
% 7.51/1.49  --inst_subs_new                         false
% 7.51/1.49  --inst_eq_res_simp                      false
% 7.51/1.49  --inst_subs_given                       false
% 7.51/1.49  --inst_orphan_elimination               true
% 7.51/1.49  --inst_learning_loop_flag               true
% 7.51/1.49  --inst_learning_start                   3000
% 7.51/1.49  --inst_learning_factor                  2
% 7.51/1.49  --inst_start_prop_sim_after_learn       3
% 7.51/1.49  --inst_sel_renew                        solver
% 7.51/1.49  --inst_lit_activity_flag                true
% 7.51/1.49  --inst_restr_to_given                   false
% 7.51/1.49  --inst_activity_threshold               500
% 7.51/1.49  --inst_out_proof                        true
% 7.51/1.49  
% 7.51/1.49  ------ Resolution Options
% 7.51/1.49  
% 7.51/1.49  --resolution_flag                       false
% 7.51/1.49  --res_lit_sel                           adaptive
% 7.51/1.49  --res_lit_sel_side                      none
% 7.51/1.49  --res_ordering                          kbo
% 7.51/1.49  --res_to_prop_solver                    active
% 7.51/1.49  --res_prop_simpl_new                    false
% 7.51/1.49  --res_prop_simpl_given                  true
% 7.51/1.49  --res_passive_queue_type                priority_queues
% 7.51/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.51/1.49  --res_passive_queues_freq               [15;5]
% 7.51/1.49  --res_forward_subs                      full
% 7.51/1.49  --res_backward_subs                     full
% 7.51/1.49  --res_forward_subs_resolution           true
% 7.51/1.49  --res_backward_subs_resolution          true
% 7.51/1.49  --res_orphan_elimination                true
% 7.51/1.49  --res_time_limit                        2.
% 7.51/1.49  --res_out_proof                         true
% 7.51/1.49  
% 7.51/1.49  ------ Superposition Options
% 7.51/1.49  
% 7.51/1.49  --superposition_flag                    true
% 7.51/1.49  --sup_passive_queue_type                priority_queues
% 7.51/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.51/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.51/1.49  --demod_completeness_check              fast
% 7.51/1.49  --demod_use_ground                      true
% 7.51/1.49  --sup_to_prop_solver                    passive
% 7.51/1.49  --sup_prop_simpl_new                    true
% 7.51/1.49  --sup_prop_simpl_given                  true
% 7.51/1.49  --sup_fun_splitting                     false
% 7.51/1.49  --sup_smt_interval                      50000
% 7.51/1.49  
% 7.51/1.49  ------ Superposition Simplification Setup
% 7.51/1.49  
% 7.51/1.49  --sup_indices_passive                   []
% 7.51/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.51/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.51/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.51/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.51/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.51/1.49  --sup_full_bw                           [BwDemod]
% 7.51/1.49  --sup_immed_triv                        [TrivRules]
% 7.51/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.51/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.51/1.49  --sup_immed_bw_main                     []
% 7.51/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.51/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.51/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.51/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.51/1.49  
% 7.51/1.49  ------ Combination Options
% 7.51/1.49  
% 7.51/1.49  --comb_res_mult                         3
% 7.51/1.49  --comb_sup_mult                         2
% 7.51/1.49  --comb_inst_mult                        10
% 7.51/1.49  
% 7.51/1.49  ------ Debug Options
% 7.51/1.49  
% 7.51/1.49  --dbg_backtrace                         false
% 7.51/1.49  --dbg_dump_prop_clauses                 false
% 7.51/1.49  --dbg_dump_prop_clauses_file            -
% 7.51/1.49  --dbg_out_stat                          false
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  ------ Proving...
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  % SZS status Theorem for theBenchmark.p
% 7.51/1.49  
% 7.51/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.51/1.49  
% 7.51/1.49  fof(f11,conjecture,(
% 7.51/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f12,negated_conjecture,(
% 7.51/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 7.51/1.49    inference(negated_conjecture,[],[f11])).
% 7.51/1.49  
% 7.51/1.49  fof(f29,plain,(
% 7.51/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.51/1.49    inference(ennf_transformation,[],[f12])).
% 7.51/1.49  
% 7.51/1.49  fof(f30,plain,(
% 7.51/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.51/1.49    inference(flattening,[],[f29])).
% 7.51/1.49  
% 7.51/1.49  fof(f37,plain,(
% 7.51/1.49    ( ! [X2,X0,X1] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(X0,X1,sK3),X2) & m1_pre_topc(sK3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 7.51/1.49    introduced(choice_axiom,[])).
% 7.51/1.49  
% 7.51/1.49  fof(f36,plain,(
% 7.51/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(X1,sK2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.51/1.49    introduced(choice_axiom,[])).
% 7.51/1.49  
% 7.51/1.49  fof(f35,plain,(
% 7.51/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 7.51/1.49    introduced(choice_axiom,[])).
% 7.51/1.49  
% 7.51/1.49  fof(f34,plain,(
% 7.51/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.51/1.49    introduced(choice_axiom,[])).
% 7.51/1.49  
% 7.51/1.49  fof(f38,plain,(
% 7.51/1.49    (((~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.51/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f37,f36,f35,f34])).
% 7.51/1.49  
% 7.51/1.49  fof(f58,plain,(
% 7.51/1.49    m1_pre_topc(sK1,sK0)),
% 7.51/1.49    inference(cnf_transformation,[],[f38])).
% 7.51/1.49  
% 7.51/1.49  fof(f62,plain,(
% 7.51/1.49    m1_pre_topc(sK3,sK0)),
% 7.51/1.49    inference(cnf_transformation,[],[f38])).
% 7.51/1.49  
% 7.51/1.49  fof(f5,axiom,(
% 7.51/1.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3))))))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f18,plain,(
% 7.51/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.51/1.49    inference(ennf_transformation,[],[f5])).
% 7.51/1.49  
% 7.51/1.49  fof(f19,plain,(
% 7.51/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.51/1.49    inference(flattening,[],[f18])).
% 7.51/1.49  
% 7.51/1.49  fof(f31,plain,(
% 7.51/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3)) & (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.51/1.49    inference(nnf_transformation,[],[f19])).
% 7.51/1.49  
% 7.51/1.49  fof(f43,plain,(
% 7.51/1.49    ( ! [X2,X0,X3,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f31])).
% 7.51/1.49  
% 7.51/1.49  fof(f66,plain,(
% 7.51/1.49    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.51/1.49    inference(equality_resolution,[],[f43])).
% 7.51/1.49  
% 7.51/1.49  fof(f6,axiom,(
% 7.51/1.49    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f20,plain,(
% 7.51/1.49    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.51/1.49    inference(ennf_transformation,[],[f6])).
% 7.51/1.49  
% 7.51/1.49  fof(f21,plain,(
% 7.51/1.49    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.51/1.49    inference(flattening,[],[f20])).
% 7.51/1.49  
% 7.51/1.49  fof(f45,plain,(
% 7.51/1.49    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f21])).
% 7.51/1.49  
% 7.51/1.49  fof(f46,plain,(
% 7.51/1.49    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f21])).
% 7.51/1.49  
% 7.51/1.49  fof(f47,plain,(
% 7.51/1.49    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f21])).
% 7.51/1.49  
% 7.51/1.49  fof(f54,plain,(
% 7.51/1.49    ~v2_struct_0(sK0)),
% 7.51/1.49    inference(cnf_transformation,[],[f38])).
% 7.51/1.49  
% 7.51/1.49  fof(f56,plain,(
% 7.51/1.49    l1_pre_topc(sK0)),
% 7.51/1.49    inference(cnf_transformation,[],[f38])).
% 7.51/1.49  
% 7.51/1.49  fof(f61,plain,(
% 7.51/1.49    ~v2_struct_0(sK3)),
% 7.51/1.49    inference(cnf_transformation,[],[f38])).
% 7.51/1.49  
% 7.51/1.49  fof(f63,plain,(
% 7.51/1.49    m1_pre_topc(sK1,sK2)),
% 7.51/1.49    inference(cnf_transformation,[],[f38])).
% 7.51/1.49  
% 7.51/1.49  fof(f64,plain,(
% 7.51/1.49    m1_pre_topc(sK3,sK2)),
% 7.51/1.49    inference(cnf_transformation,[],[f38])).
% 7.51/1.49  
% 7.51/1.49  fof(f59,plain,(
% 7.51/1.49    ~v2_struct_0(sK2)),
% 7.51/1.49    inference(cnf_transformation,[],[f38])).
% 7.51/1.49  
% 7.51/1.49  fof(f60,plain,(
% 7.51/1.49    m1_pre_topc(sK2,sK0)),
% 7.51/1.49    inference(cnf_transformation,[],[f38])).
% 7.51/1.49  
% 7.51/1.49  fof(f2,axiom,(
% 7.51/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f14,plain,(
% 7.51/1.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.51/1.49    inference(ennf_transformation,[],[f2])).
% 7.51/1.49  
% 7.51/1.49  fof(f40,plain,(
% 7.51/1.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f14])).
% 7.51/1.49  
% 7.51/1.49  fof(f57,plain,(
% 7.51/1.49    ~v2_struct_0(sK1)),
% 7.51/1.49    inference(cnf_transformation,[],[f38])).
% 7.51/1.49  
% 7.51/1.49  fof(f4,axiom,(
% 7.51/1.49    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f16,plain,(
% 7.51/1.49    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.51/1.49    inference(ennf_transformation,[],[f4])).
% 7.51/1.49  
% 7.51/1.49  fof(f17,plain,(
% 7.51/1.49    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.51/1.49    inference(flattening,[],[f16])).
% 7.51/1.49  
% 7.51/1.49  fof(f42,plain,(
% 7.51/1.49    ( ! [X2,X0,X1] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f17])).
% 7.51/1.49  
% 7.51/1.49  fof(f7,axiom,(
% 7.51/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)))))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f22,plain,(
% 7.51/1.49    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.51/1.49    inference(ennf_transformation,[],[f7])).
% 7.51/1.49  
% 7.51/1.49  fof(f23,plain,(
% 7.51/1.49    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.51/1.49    inference(flattening,[],[f22])).
% 7.51/1.49  
% 7.51/1.49  fof(f32,plain,(
% 7.51/1.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_tsep_1(X0,X1,X2)) & (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) | ~m1_pre_topc(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.51/1.49    inference(nnf_transformation,[],[f23])).
% 7.51/1.49  
% 7.51/1.49  fof(f48,plain,(
% 7.51/1.49    ( ! [X2,X0,X1] : (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f32])).
% 7.51/1.49  
% 7.51/1.49  fof(f55,plain,(
% 7.51/1.49    v2_pre_topc(sK0)),
% 7.51/1.49    inference(cnf_transformation,[],[f38])).
% 7.51/1.49  
% 7.51/1.49  fof(f8,axiom,(
% 7.51/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f24,plain,(
% 7.51/1.49    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.51/1.49    inference(ennf_transformation,[],[f8])).
% 7.51/1.49  
% 7.51/1.49  fof(f25,plain,(
% 7.51/1.49    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.51/1.49    inference(flattening,[],[f24])).
% 7.51/1.49  
% 7.51/1.49  fof(f50,plain,(
% 7.51/1.49    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f25])).
% 7.51/1.49  
% 7.51/1.49  fof(f1,axiom,(
% 7.51/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f13,plain,(
% 7.51/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 7.51/1.49    inference(ennf_transformation,[],[f1])).
% 7.51/1.49  
% 7.51/1.49  fof(f39,plain,(
% 7.51/1.50    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 7.51/1.50    inference(cnf_transformation,[],[f13])).
% 7.51/1.50  
% 7.51/1.50  fof(f10,axiom,(
% 7.51/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 7.51/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.50  
% 7.51/1.50  fof(f27,plain,(
% 7.51/1.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.51/1.50    inference(ennf_transformation,[],[f10])).
% 7.51/1.50  
% 7.51/1.50  fof(f28,plain,(
% 7.51/1.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.51/1.50    inference(flattening,[],[f27])).
% 7.51/1.50  
% 7.51/1.50  fof(f33,plain,(
% 7.51/1.50    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.51/1.50    inference(nnf_transformation,[],[f28])).
% 7.51/1.50  
% 7.51/1.50  fof(f52,plain,(
% 7.51/1.50    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.51/1.50    inference(cnf_transformation,[],[f33])).
% 7.51/1.50  
% 7.51/1.50  fof(f53,plain,(
% 7.51/1.50    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.51/1.50    inference(cnf_transformation,[],[f33])).
% 7.51/1.50  
% 7.51/1.50  fof(f3,axiom,(
% 7.51/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 7.51/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.50  
% 7.51/1.50  fof(f15,plain,(
% 7.51/1.50    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 7.51/1.50    inference(ennf_transformation,[],[f3])).
% 7.51/1.50  
% 7.51/1.50  fof(f41,plain,(
% 7.51/1.50    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 7.51/1.50    inference(cnf_transformation,[],[f15])).
% 7.51/1.50  
% 7.51/1.50  fof(f65,plain,(
% 7.51/1.50    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 7.51/1.50    inference(cnf_transformation,[],[f38])).
% 7.51/1.50  
% 7.51/1.50  cnf(c_22,negated_conjecture,
% 7.51/1.50      ( m1_pre_topc(sK1,sK0) ),
% 7.51/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_716,negated_conjecture,
% 7.51/1.50      ( m1_pre_topc(sK1,sK0) ),
% 7.51/1.50      inference(subtyping,[status(esa)],[c_22]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1220,plain,
% 7.51/1.50      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_18,negated_conjecture,
% 7.51/1.50      ( m1_pre_topc(sK3,sK0) ),
% 7.51/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_720,negated_conjecture,
% 7.51/1.50      ( m1_pre_topc(sK3,sK0) ),
% 7.51/1.50      inference(subtyping,[status(esa)],[c_18]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1216,plain,
% 7.51/1.50      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_720]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_pre_topc(X2,X1)
% 7.51/1.50      | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 7.51/1.50      | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 7.51/1.50      | v2_struct_0(X1)
% 7.51/1.50      | v2_struct_0(X0)
% 7.51/1.50      | v2_struct_0(X2)
% 7.51/1.50      | v2_struct_0(k1_tsep_1(X1,X0,X2))
% 7.51/1.50      | ~ l1_pre_topc(X1)
% 7.51/1.50      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 7.51/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_8,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_pre_topc(X2,X1)
% 7.51/1.50      | v2_struct_0(X1)
% 7.51/1.50      | v2_struct_0(X0)
% 7.51/1.50      | v2_struct_0(X2)
% 7.51/1.50      | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
% 7.51/1.50      | ~ l1_pre_topc(X1) ),
% 7.51/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_7,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_pre_topc(X2,X1)
% 7.51/1.50      | v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 7.51/1.50      | v2_struct_0(X1)
% 7.51/1.50      | v2_struct_0(X0)
% 7.51/1.50      | v2_struct_0(X2)
% 7.51/1.50      | ~ l1_pre_topc(X1) ),
% 7.51/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_6,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_pre_topc(X2,X1)
% 7.51/1.50      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 7.51/1.50      | v2_struct_0(X1)
% 7.51/1.50      | v2_struct_0(X0)
% 7.51/1.50      | v2_struct_0(X2)
% 7.51/1.50      | ~ l1_pre_topc(X1) ),
% 7.51/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_150,plain,
% 7.51/1.50      ( v2_struct_0(X2)
% 7.51/1.50      | v2_struct_0(X0)
% 7.51/1.50      | v2_struct_0(X1)
% 7.51/1.50      | ~ m1_pre_topc(X2,X1)
% 7.51/1.50      | ~ m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ l1_pre_topc(X1)
% 7.51/1.50      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_5,c_8,c_7,c_6]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_151,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_pre_topc(X2,X1)
% 7.51/1.50      | v2_struct_0(X0)
% 7.51/1.50      | v2_struct_0(X2)
% 7.51/1.50      | v2_struct_0(X1)
% 7.51/1.50      | ~ l1_pre_topc(X1)
% 7.51/1.50      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 7.51/1.50      inference(renaming,[status(thm)],[c_150]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_712,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 7.51/1.50      | ~ m1_pre_topc(X2_43,X1_43)
% 7.51/1.50      | v2_struct_0(X0_43)
% 7.51/1.50      | v2_struct_0(X1_43)
% 7.51/1.50      | v2_struct_0(X2_43)
% 7.51/1.50      | ~ l1_pre_topc(X1_43)
% 7.51/1.50      | u1_struct_0(k1_tsep_1(X1_43,X0_43,X2_43)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X2_43)) ),
% 7.51/1.50      inference(subtyping,[status(esa)],[c_151]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1224,plain,
% 7.51/1.50      ( u1_struct_0(k1_tsep_1(X0_43,X1_43,X2_43)) = k2_xboole_0(u1_struct_0(X1_43),u1_struct_0(X2_43))
% 7.51/1.50      | m1_pre_topc(X1_43,X0_43) != iProver_top
% 7.51/1.50      | m1_pre_topc(X2_43,X0_43) != iProver_top
% 7.51/1.50      | v2_struct_0(X0_43) = iProver_top
% 7.51/1.50      | v2_struct_0(X1_43) = iProver_top
% 7.51/1.50      | v2_struct_0(X2_43) = iProver_top
% 7.51/1.50      | l1_pre_topc(X0_43) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_712]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4414,plain,
% 7.51/1.50      ( u1_struct_0(k1_tsep_1(sK0,X0_43,sK3)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3))
% 7.51/1.50      | m1_pre_topc(X0_43,sK0) != iProver_top
% 7.51/1.50      | v2_struct_0(X0_43) = iProver_top
% 7.51/1.50      | v2_struct_0(sK3) = iProver_top
% 7.51/1.50      | v2_struct_0(sK0) = iProver_top
% 7.51/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_1216,c_1224]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_26,negated_conjecture,
% 7.51/1.50      ( ~ v2_struct_0(sK0) ),
% 7.51/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_27,plain,
% 7.51/1.50      ( v2_struct_0(sK0) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_24,negated_conjecture,
% 7.51/1.50      ( l1_pre_topc(sK0) ),
% 7.51/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_29,plain,
% 7.51/1.50      ( l1_pre_topc(sK0) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_19,negated_conjecture,
% 7.51/1.50      ( ~ v2_struct_0(sK3) ),
% 7.51/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_34,plain,
% 7.51/1.50      ( v2_struct_0(sK3) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5450,plain,
% 7.51/1.50      ( v2_struct_0(X0_43) = iProver_top
% 7.51/1.50      | m1_pre_topc(X0_43,sK0) != iProver_top
% 7.51/1.50      | u1_struct_0(k1_tsep_1(sK0,X0_43,sK3)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3)) ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_4414,c_27,c_29,c_34]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5451,plain,
% 7.51/1.50      ( u1_struct_0(k1_tsep_1(sK0,X0_43,sK3)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3))
% 7.51/1.50      | m1_pre_topc(X0_43,sK0) != iProver_top
% 7.51/1.50      | v2_struct_0(X0_43) = iProver_top ),
% 7.51/1.50      inference(renaming,[status(thm)],[c_5450]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5461,plain,
% 7.51/1.50      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
% 7.51/1.50      | v2_struct_0(sK1) = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_1220,c_5451]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_17,negated_conjecture,
% 7.51/1.50      ( m1_pre_topc(sK1,sK2) ),
% 7.51/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_721,negated_conjecture,
% 7.51/1.50      ( m1_pre_topc(sK1,sK2) ),
% 7.51/1.50      inference(subtyping,[status(esa)],[c_17]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1215,plain,
% 7.51/1.50      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_721]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_16,negated_conjecture,
% 7.51/1.50      ( m1_pre_topc(sK3,sK2) ),
% 7.51/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_722,negated_conjecture,
% 7.51/1.50      ( m1_pre_topc(sK3,sK2) ),
% 7.51/1.50      inference(subtyping,[status(esa)],[c_16]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1214,plain,
% 7.51/1.50      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_722]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4412,plain,
% 7.51/1.50      ( u1_struct_0(k1_tsep_1(sK2,X0_43,sK3)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3))
% 7.51/1.50      | m1_pre_topc(X0_43,sK2) != iProver_top
% 7.51/1.50      | v2_struct_0(X0_43) = iProver_top
% 7.51/1.50      | v2_struct_0(sK2) = iProver_top
% 7.51/1.50      | v2_struct_0(sK3) = iProver_top
% 7.51/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_1214,c_1224]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_21,negated_conjecture,
% 7.51/1.50      ( ~ v2_struct_0(sK2) ),
% 7.51/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_32,plain,
% 7.51/1.50      ( v2_struct_0(sK2) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_20,negated_conjecture,
% 7.51/1.50      ( m1_pre_topc(sK2,sK0) ),
% 7.51/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_33,plain,
% 7.51/1.50      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.51/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_731,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 7.51/1.50      | ~ l1_pre_topc(X1_43)
% 7.51/1.50      | l1_pre_topc(X0_43) ),
% 7.51/1.50      inference(subtyping,[status(esa)],[c_1]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1540,plain,
% 7.51/1.50      ( ~ m1_pre_topc(sK2,X0_43)
% 7.51/1.50      | ~ l1_pre_topc(X0_43)
% 7.51/1.50      | l1_pre_topc(sK2) ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_731]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1541,plain,
% 7.51/1.50      ( m1_pre_topc(sK2,X0_43) != iProver_top
% 7.51/1.50      | l1_pre_topc(X0_43) != iProver_top
% 7.51/1.50      | l1_pre_topc(sK2) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_1540]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1543,plain,
% 7.51/1.50      ( m1_pre_topc(sK2,sK0) != iProver_top
% 7.51/1.50      | l1_pre_topc(sK2) = iProver_top
% 7.51/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_1541]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5034,plain,
% 7.51/1.50      ( v2_struct_0(X0_43) = iProver_top
% 7.51/1.50      | m1_pre_topc(X0_43,sK2) != iProver_top
% 7.51/1.50      | u1_struct_0(k1_tsep_1(sK2,X0_43,sK3)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3)) ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_4412,c_29,c_32,c_33,c_34,c_1543]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5035,plain,
% 7.51/1.50      ( u1_struct_0(k1_tsep_1(sK2,X0_43,sK3)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3))
% 7.51/1.50      | m1_pre_topc(X0_43,sK2) != iProver_top
% 7.51/1.50      | v2_struct_0(X0_43) = iProver_top ),
% 7.51/1.50      inference(renaming,[status(thm)],[c_5034]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5044,plain,
% 7.51/1.50      ( u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
% 7.51/1.50      | v2_struct_0(sK1) = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_1215,c_5035]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_23,negated_conjecture,
% 7.51/1.50      ( ~ v2_struct_0(sK1) ),
% 7.51/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_30,plain,
% 7.51/1.50      ( v2_struct_0(sK1) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5147,plain,
% 7.51/1.50      ( u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_5044,c_30]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5488,plain,
% 7.51/1.50      ( u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 7.51/1.50      | v2_struct_0(sK1) = iProver_top ),
% 7.51/1.50      inference(demodulation,[status(thm)],[c_5461,c_5147]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_14609,plain,
% 7.51/1.50      ( u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_5488,c_30]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_14618,plain,
% 7.51/1.50      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
% 7.51/1.50      inference(demodulation,[status(thm)],[c_14609,c_5147]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_718,negated_conjecture,
% 7.51/1.50      ( m1_pre_topc(sK2,sK0) ),
% 7.51/1.50      inference(subtyping,[status(esa)],[c_20]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1218,plain,
% 7.51/1.50      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_718]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5460,plain,
% 7.51/1.50      ( u1_struct_0(k1_tsep_1(sK0,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
% 7.51/1.50      | v2_struct_0(sK2) = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_1218,c_5451]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_3,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_pre_topc(X2,X1)
% 7.51/1.50      | v2_struct_0(X1)
% 7.51/1.50      | v2_struct_0(X0)
% 7.51/1.50      | v2_struct_0(X2)
% 7.51/1.50      | ~ l1_pre_topc(X1)
% 7.51/1.50      | k1_tsep_1(X1,X2,X0) = k1_tsep_1(X1,X0,X2) ),
% 7.51/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_729,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 7.51/1.50      | ~ m1_pre_topc(X2_43,X1_43)
% 7.51/1.50      | v2_struct_0(X0_43)
% 7.51/1.50      | v2_struct_0(X1_43)
% 7.51/1.50      | v2_struct_0(X2_43)
% 7.51/1.50      | ~ l1_pre_topc(X1_43)
% 7.51/1.50      | k1_tsep_1(X1_43,X2_43,X0_43) = k1_tsep_1(X1_43,X0_43,X2_43) ),
% 7.51/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1207,plain,
% 7.51/1.50      ( k1_tsep_1(X0_43,X1_43,X2_43) = k1_tsep_1(X0_43,X2_43,X1_43)
% 7.51/1.50      | m1_pre_topc(X2_43,X0_43) != iProver_top
% 7.51/1.50      | m1_pre_topc(X1_43,X0_43) != iProver_top
% 7.51/1.50      | v2_struct_0(X0_43) = iProver_top
% 7.51/1.50      | v2_struct_0(X2_43) = iProver_top
% 7.51/1.50      | v2_struct_0(X1_43) = iProver_top
% 7.51/1.50      | l1_pre_topc(X0_43) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_3187,plain,
% 7.51/1.50      ( k1_tsep_1(sK0,sK3,X0_43) = k1_tsep_1(sK0,X0_43,sK3)
% 7.51/1.50      | m1_pre_topc(X0_43,sK0) != iProver_top
% 7.51/1.50      | v2_struct_0(X0_43) = iProver_top
% 7.51/1.50      | v2_struct_0(sK3) = iProver_top
% 7.51/1.50      | v2_struct_0(sK0) = iProver_top
% 7.51/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_1216,c_1207]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4039,plain,
% 7.51/1.50      ( v2_struct_0(X0_43) = iProver_top
% 7.51/1.50      | m1_pre_topc(X0_43,sK0) != iProver_top
% 7.51/1.50      | k1_tsep_1(sK0,sK3,X0_43) = k1_tsep_1(sK0,X0_43,sK3) ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_3187,c_27,c_29,c_34]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4040,plain,
% 7.51/1.50      ( k1_tsep_1(sK0,sK3,X0_43) = k1_tsep_1(sK0,X0_43,sK3)
% 7.51/1.50      | m1_pre_topc(X0_43,sK0) != iProver_top
% 7.51/1.50      | v2_struct_0(X0_43) = iProver_top ),
% 7.51/1.50      inference(renaming,[status(thm)],[c_4039]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4049,plain,
% 7.51/1.50      ( k1_tsep_1(sK0,sK2,sK3) = k1_tsep_1(sK0,sK3,sK2)
% 7.51/1.50      | v2_struct_0(sK2) = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_1218,c_4040]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4168,plain,
% 7.51/1.50      ( k1_tsep_1(sK0,sK2,sK3) = k1_tsep_1(sK0,sK3,sK2) ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_4049,c_32]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5493,plain,
% 7.51/1.50      ( u1_struct_0(k1_tsep_1(sK0,sK3,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
% 7.51/1.50      | v2_struct_0(sK2) = iProver_top ),
% 7.51/1.50      inference(light_normalisation,[status(thm)],[c_5460,c_4168]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_18881,plain,
% 7.51/1.50      ( u1_struct_0(k1_tsep_1(sK0,sK3,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_5493,c_32]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_10,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_pre_topc(X2,X1)
% 7.51/1.50      | ~ m1_pre_topc(X0,X2)
% 7.51/1.50      | ~ v2_pre_topc(X1)
% 7.51/1.50      | v2_struct_0(X1)
% 7.51/1.50      | v2_struct_0(X0)
% 7.51/1.50      | v2_struct_0(X2)
% 7.51/1.50      | ~ l1_pre_topc(X1)
% 7.51/1.50      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X1,X0,X2) ),
% 7.51/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_25,negated_conjecture,
% 7.51/1.50      ( v2_pre_topc(sK0) ),
% 7.51/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_405,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_pre_topc(X2,X1)
% 7.51/1.50      | ~ m1_pre_topc(X0,X2)
% 7.51/1.50      | v2_struct_0(X0)
% 7.51/1.50      | v2_struct_0(X2)
% 7.51/1.50      | v2_struct_0(X1)
% 7.51/1.50      | ~ l1_pre_topc(X1)
% 7.51/1.50      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X1,X0,X2)
% 7.51/1.50      | sK0 != X1 ),
% 7.51/1.50      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_406,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_pre_topc(X1,sK0)
% 7.51/1.50      | ~ m1_pre_topc(X0,sK0)
% 7.51/1.50      | v2_struct_0(X0)
% 7.51/1.50      | v2_struct_0(X1)
% 7.51/1.50      | v2_struct_0(sK0)
% 7.51/1.50      | ~ l1_pre_topc(sK0)
% 7.51/1.50      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X0,X1) ),
% 7.51/1.50      inference(unflattening,[status(thm)],[c_405]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_408,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_pre_topc(X1,sK0)
% 7.51/1.50      | ~ m1_pre_topc(X0,sK0)
% 7.51/1.50      | v2_struct_0(X0)
% 7.51/1.50      | v2_struct_0(X1)
% 7.51/1.50      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X0,X1) ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_406,c_26,c_24]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_409,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_pre_topc(X0,sK0)
% 7.51/1.50      | ~ m1_pre_topc(X1,sK0)
% 7.51/1.50      | v2_struct_0(X0)
% 7.51/1.50      | v2_struct_0(X1)
% 7.51/1.50      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X0,X1) ),
% 7.51/1.50      inference(renaming,[status(thm)],[c_408]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_708,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 7.51/1.50      | ~ m1_pre_topc(X0_43,sK0)
% 7.51/1.50      | ~ m1_pre_topc(X1_43,sK0)
% 7.51/1.50      | v2_struct_0(X0_43)
% 7.51/1.50      | v2_struct_0(X1_43)
% 7.51/1.50      | g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43)) = k1_tsep_1(sK0,X0_43,X1_43) ),
% 7.51/1.50      inference(subtyping,[status(esa)],[c_409]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1228,plain,
% 7.51/1.50      ( g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(sK0,X1_43,X0_43)
% 7.51/1.50      | m1_pre_topc(X1_43,X0_43) != iProver_top
% 7.51/1.50      | m1_pre_topc(X0_43,sK0) != iProver_top
% 7.51/1.50      | m1_pre_topc(X1_43,sK0) != iProver_top
% 7.51/1.50      | v2_struct_0(X0_43) = iProver_top
% 7.51/1.50      | v2_struct_0(X1_43) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_708]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_2731,plain,
% 7.51/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK3,sK2)
% 7.51/1.50      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.51/1.50      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.51/1.50      | v2_struct_0(sK2) = iProver_top
% 7.51/1.50      | v2_struct_0(sK3) = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_1214,c_1228]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_11,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ v2_pre_topc(X1)
% 7.51/1.50      | v2_struct_0(X1)
% 7.51/1.50      | v2_struct_0(X0)
% 7.51/1.50      | ~ l1_pre_topc(X1)
% 7.51/1.50      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
% 7.51/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_384,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.51/1.50      | v2_struct_0(X0)
% 7.51/1.50      | v2_struct_0(X1)
% 7.51/1.50      | ~ l1_pre_topc(X1)
% 7.51/1.50      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
% 7.51/1.50      | sK0 != X1 ),
% 7.51/1.50      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_385,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,sK0)
% 7.51/1.50      | v2_struct_0(X0)
% 7.51/1.50      | v2_struct_0(sK0)
% 7.51/1.50      | ~ l1_pre_topc(sK0)
% 7.51/1.50      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) ),
% 7.51/1.50      inference(unflattening,[status(thm)],[c_384]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_389,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,sK0)
% 7.51/1.50      | v2_struct_0(X0)
% 7.51/1.50      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_385,c_26,c_24]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_709,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0_43,sK0)
% 7.51/1.50      | v2_struct_0(X0_43)
% 7.51/1.50      | g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(sK0,X0_43,X0_43) ),
% 7.51/1.50      inference(subtyping,[status(esa)],[c_389]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1227,plain,
% 7.51/1.50      ( g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(sK0,X0_43,X0_43)
% 7.51/1.50      | m1_pre_topc(X0_43,sK0) != iProver_top
% 7.51/1.50      | v2_struct_0(X0_43) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_709]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_2113,plain,
% 7.51/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
% 7.51/1.50      | v2_struct_0(sK2) = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_1218,c_1227]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1783,plain,
% 7.51/1.50      ( ~ m1_pre_topc(sK2,sK0)
% 7.51/1.50      | v2_struct_0(sK2)
% 7.51/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_709]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_2569,plain,
% 7.51/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_2113,c_21,c_20,c_1783]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_2804,plain,
% 7.51/1.50      ( k1_tsep_1(sK0,sK3,sK2) = k1_tsep_1(sK0,sK2,sK2)
% 7.51/1.50      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.51/1.50      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.51/1.50      | v2_struct_0(sK2) = iProver_top
% 7.51/1.50      | v2_struct_0(sK3) = iProver_top ),
% 7.51/1.50      inference(demodulation,[status(thm)],[c_2731,c_2569]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_35,plain,
% 7.51/1.50      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_15891,plain,
% 7.51/1.50      ( k1_tsep_1(sK0,sK3,sK2) = k1_tsep_1(sK0,sK2,sK2) ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_2804,c_32,c_33,c_34,c_35]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_2732,plain,
% 7.51/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2)
% 7.51/1.50      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.51/1.50      | m1_pre_topc(sK1,sK0) != iProver_top
% 7.51/1.50      | v2_struct_0(sK2) = iProver_top
% 7.51/1.50      | v2_struct_0(sK1) = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_1215,c_1228]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_2793,plain,
% 7.51/1.50      ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK2)
% 7.51/1.50      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.51/1.50      | m1_pre_topc(sK1,sK0) != iProver_top
% 7.51/1.50      | v2_struct_0(sK2) = iProver_top
% 7.51/1.50      | v2_struct_0(sK1) = iProver_top ),
% 7.51/1.50      inference(demodulation,[status(thm)],[c_2732,c_2569]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_31,plain,
% 7.51/1.50      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_14891,plain,
% 7.51/1.50      ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK2) ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_2793,c_30,c_31,c_32,c_33]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_15893,plain,
% 7.51/1.50      ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK3,sK2) ),
% 7.51/1.50      inference(light_normalisation,[status(thm)],[c_15891,c_14891]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_18883,plain,
% 7.51/1.50      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 7.51/1.50      inference(light_normalisation,[status(thm)],[c_18881,c_15893]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_0,plain,
% 7.51/1.50      ( ~ r1_tarski(X0,X1)
% 7.51/1.50      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
% 7.51/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_732,plain,
% 7.51/1.50      ( ~ r1_tarski(X0_44,X1_44)
% 7.51/1.50      | r1_tarski(k2_xboole_0(X0_44,X2_44),k2_xboole_0(X1_44,X2_44)) ),
% 7.51/1.50      inference(subtyping,[status(esa)],[c_0]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1204,plain,
% 7.51/1.50      ( r1_tarski(X0_44,X1_44) != iProver_top
% 7.51/1.50      | r1_tarski(k2_xboole_0(X0_44,X2_44),k2_xboole_0(X1_44,X2_44)) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_18886,plain,
% 7.51/1.50      ( r1_tarski(X0_44,u1_struct_0(sK2)) != iProver_top
% 7.51/1.50      | r1_tarski(k2_xboole_0(X0_44,u1_struct_0(sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) = iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_18883,c_1204]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_19310,plain,
% 7.51/1.50      ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) = iProver_top
% 7.51/1.50      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_14618,c_18886]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_727,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 7.51/1.50      | ~ m1_pre_topc(X2_43,X1_43)
% 7.51/1.50      | m1_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43),X1_43)
% 7.51/1.50      | v2_struct_0(X0_43)
% 7.51/1.50      | v2_struct_0(X1_43)
% 7.51/1.50      | v2_struct_0(X2_43)
% 7.51/1.50      | ~ l1_pre_topc(X1_43) ),
% 7.51/1.50      inference(subtyping,[status(esa)],[c_6]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4805,plain,
% 7.51/1.50      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
% 7.51/1.50      | ~ m1_pre_topc(sK2,sK0)
% 7.51/1.50      | ~ m1_pre_topc(sK1,sK0)
% 7.51/1.50      | v2_struct_0(sK2)
% 7.51/1.50      | v2_struct_0(sK1)
% 7.51/1.50      | v2_struct_0(sK0)
% 7.51/1.50      | ~ l1_pre_topc(sK0) ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_727]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4808,plain,
% 7.51/1.50      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) = iProver_top
% 7.51/1.50      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.51/1.50      | m1_pre_topc(sK1,sK0) != iProver_top
% 7.51/1.50      | v2_struct_0(sK2) = iProver_top
% 7.51/1.50      | v2_struct_0(sK1) = iProver_top
% 7.51/1.50      | v2_struct_0(sK0) = iProver_top
% 7.51/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_4805]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_14,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_pre_topc(X2,X1)
% 7.51/1.50      | m1_pre_topc(X0,X2)
% 7.51/1.50      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 7.51/1.50      | ~ v2_pre_topc(X1)
% 7.51/1.50      | ~ l1_pre_topc(X1) ),
% 7.51/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_340,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_pre_topc(X2,X1)
% 7.51/1.50      | m1_pre_topc(X0,X2)
% 7.51/1.50      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 7.51/1.50      | ~ l1_pre_topc(X1)
% 7.51/1.50      | sK0 != X1 ),
% 7.51/1.50      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_341,plain,
% 7.51/1.50      ( m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_pre_topc(X1,sK0)
% 7.51/1.50      | ~ m1_pre_topc(X0,sK0)
% 7.51/1.50      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.51/1.50      | ~ l1_pre_topc(sK0) ),
% 7.51/1.50      inference(unflattening,[status(thm)],[c_340]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_343,plain,
% 7.51/1.50      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.51/1.50      | ~ m1_pre_topc(X0,sK0)
% 7.51/1.50      | ~ m1_pre_topc(X1,sK0)
% 7.51/1.50      | m1_pre_topc(X0,X1) ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_341,c_24]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_344,plain,
% 7.51/1.50      ( m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_pre_topc(X0,sK0)
% 7.51/1.50      | ~ m1_pre_topc(X1,sK0)
% 7.51/1.50      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
% 7.51/1.50      inference(renaming,[status(thm)],[c_343]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_711,plain,
% 7.51/1.50      ( m1_pre_topc(X0_43,X1_43)
% 7.51/1.50      | ~ m1_pre_topc(X0_43,sK0)
% 7.51/1.50      | ~ m1_pre_topc(X1_43,sK0)
% 7.51/1.50      | ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
% 7.51/1.50      inference(subtyping,[status(esa)],[c_344]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_3877,plain,
% 7.51/1.50      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
% 7.51/1.50      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2))
% 7.51/1.50      | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 7.51/1.50      | ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_711]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_3878,plain,
% 7.51/1.50      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
% 7.51/1.50      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2)) = iProver_top
% 7.51/1.50      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) != iProver_top
% 7.51/1.50      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_3877]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_742,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 7.51/1.50      | m1_pre_topc(X2_43,X3_43)
% 7.51/1.50      | X2_43 != X0_43
% 7.51/1.50      | X3_43 != X1_43 ),
% 7.51/1.50      theory(equality) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1639,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 7.51/1.50      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.51/1.50      | k1_tsep_1(sK0,sK1,sK3) != X0_43
% 7.51/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X1_43 ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_742]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1762,plain,
% 7.51/1.50      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_43)
% 7.51/1.50      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.51/1.50      | k1_tsep_1(sK0,sK1,sK3) != k1_tsep_1(sK0,sK1,sK3)
% 7.51/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0_43 ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_1639]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_2298,plain,
% 7.51/1.50      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2))
% 7.51/1.50      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.51/1.50      | k1_tsep_1(sK0,sK1,sK3) != k1_tsep_1(sK0,sK1,sK3)
% 7.51/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK1,sK2) ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_1762]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_2302,plain,
% 7.51/1.50      ( k1_tsep_1(sK0,sK1,sK3) != k1_tsep_1(sK0,sK1,sK3)
% 7.51/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK1,sK2)
% 7.51/1.50      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2)) != iProver_top
% 7.51/1.50      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_2298]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1777,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0_43,sK2)
% 7.51/1.50      | ~ m1_pre_topc(X0_43,sK0)
% 7.51/1.50      | ~ m1_pre_topc(sK2,sK0)
% 7.51/1.50      | v2_struct_0(X0_43)
% 7.51/1.50      | v2_struct_0(sK2)
% 7.51/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,X0_43,sK2) ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_708]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_2079,plain,
% 7.51/1.50      ( ~ m1_pre_topc(sK2,sK0)
% 7.51/1.50      | ~ m1_pre_topc(sK1,sK2)
% 7.51/1.50      | ~ m1_pre_topc(sK1,sK0)
% 7.51/1.50      | v2_struct_0(sK2)
% 7.51/1.50      | v2_struct_0(sK1)
% 7.51/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2) ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_1777]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_13,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_pre_topc(X2,X1)
% 7.51/1.50      | ~ m1_pre_topc(X0,X2)
% 7.51/1.50      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 7.51/1.50      | ~ v2_pre_topc(X1)
% 7.51/1.50      | ~ l1_pre_topc(X1) ),
% 7.51/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_360,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_pre_topc(X2,X1)
% 7.51/1.50      | ~ m1_pre_topc(X0,X2)
% 7.51/1.50      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 7.51/1.50      | ~ l1_pre_topc(X1)
% 7.51/1.50      | sK0 != X1 ),
% 7.51/1.50      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_361,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_pre_topc(X1,sK0)
% 7.51/1.50      | ~ m1_pre_topc(X0,sK0)
% 7.51/1.50      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.51/1.50      | ~ l1_pre_topc(sK0) ),
% 7.51/1.50      inference(unflattening,[status(thm)],[c_360]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_365,plain,
% 7.51/1.50      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.51/1.50      | ~ m1_pre_topc(X0,sK0)
% 7.51/1.50      | ~ m1_pre_topc(X1,sK0)
% 7.51/1.50      | ~ m1_pre_topc(X0,X1) ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_361,c_24]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_366,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_pre_topc(X0,sK0)
% 7.51/1.50      | ~ m1_pre_topc(X1,sK0)
% 7.51/1.50      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
% 7.51/1.50      inference(renaming,[status(thm)],[c_365]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_710,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 7.51/1.50      | ~ m1_pre_topc(X0_43,sK0)
% 7.51/1.50      | ~ m1_pre_topc(X1_43,sK0)
% 7.51/1.50      | r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
% 7.51/1.50      inference(subtyping,[status(esa)],[c_366]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1749,plain,
% 7.51/1.50      ( ~ m1_pre_topc(X0_43,sK2)
% 7.51/1.50      | ~ m1_pre_topc(X0_43,sK0)
% 7.51/1.50      | ~ m1_pre_topc(sK2,sK0)
% 7.51/1.50      | r1_tarski(u1_struct_0(X0_43),u1_struct_0(sK2)) ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_710]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_2048,plain,
% 7.51/1.50      ( ~ m1_pre_topc(sK2,sK0)
% 7.51/1.50      | ~ m1_pre_topc(sK1,sK2)
% 7.51/1.50      | ~ m1_pre_topc(sK1,sK0)
% 7.51/1.50      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_1749]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_2049,plain,
% 7.51/1.50      ( m1_pre_topc(sK2,sK0) != iProver_top
% 7.51/1.50      | m1_pre_topc(sK1,sK2) != iProver_top
% 7.51/1.50      | m1_pre_topc(sK1,sK0) != iProver_top
% 7.51/1.50      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_2048]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_734,plain,( X0_43 = X0_43 ),theory(equality) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1763,plain,
% 7.51/1.50      ( k1_tsep_1(sK0,sK1,sK3) = k1_tsep_1(sK0,sK1,sK3) ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_734]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1522,plain,
% 7.51/1.50      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 7.51/1.50      | ~ m1_pre_topc(sK3,sK0)
% 7.51/1.50      | ~ m1_pre_topc(sK1,sK0)
% 7.51/1.50      | v2_struct_0(sK3)
% 7.51/1.50      | v2_struct_0(sK1)
% 7.51/1.50      | v2_struct_0(sK0)
% 7.51/1.50      | ~ l1_pre_topc(sK0) ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_727]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1523,plain,
% 7.51/1.50      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) = iProver_top
% 7.51/1.50      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.51/1.50      | m1_pre_topc(sK1,sK0) != iProver_top
% 7.51/1.50      | v2_struct_0(sK3) = iProver_top
% 7.51/1.50      | v2_struct_0(sK1) = iProver_top
% 7.51/1.50      | v2_struct_0(sK0) = iProver_top
% 7.51/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_1522]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_2,plain,
% 7.51/1.50      ( m1_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.51/1.50      | ~ l1_pre_topc(X1) ),
% 7.51/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_730,plain,
% 7.51/1.50      ( m1_pre_topc(X0_43,X1_43)
% 7.51/1.50      | ~ m1_pre_topc(X0_43,g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43)))
% 7.51/1.50      | ~ l1_pre_topc(X1_43) ),
% 7.51/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1481,plain,
% 7.51/1.50      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.51/1.50      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
% 7.51/1.50      | ~ l1_pre_topc(sK2) ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_730]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1482,plain,
% 7.51/1.50      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.51/1.50      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) = iProver_top
% 7.51/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_1481]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_15,negated_conjecture,
% 7.51/1.50      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
% 7.51/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_38,plain,
% 7.51/1.50      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_36,plain,
% 7.51/1.50      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(contradiction,plain,
% 7.51/1.50      ( $false ),
% 7.51/1.50      inference(minisat,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_19310,c_4808,c_3878,c_2302,c_2079,c_2049,c_1763,
% 7.51/1.50                 c_1543,c_1523,c_1482,c_38,c_36,c_17,c_35,c_34,c_33,c_20,
% 7.51/1.50                 c_32,c_21,c_31,c_22,c_30,c_23,c_29,c_27]) ).
% 7.51/1.50  
% 7.51/1.50  
% 7.51/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.51/1.50  
% 7.51/1.50  ------                               Statistics
% 7.51/1.50  
% 7.51/1.50  ------ General
% 7.51/1.50  
% 7.51/1.50  abstr_ref_over_cycles:                  0
% 7.51/1.50  abstr_ref_under_cycles:                 0
% 7.51/1.50  gc_basic_clause_elim:                   0
% 7.51/1.50  forced_gc_time:                         0
% 7.51/1.50  parsing_time:                           0.012
% 7.51/1.50  unif_index_cands_time:                  0.
% 7.51/1.50  unif_index_add_time:                    0.
% 7.51/1.50  orderings_time:                         0.
% 7.51/1.50  out_proof_time:                         0.018
% 7.51/1.50  total_time:                             0.558
% 7.51/1.50  num_of_symbols:                         49
% 7.51/1.50  num_of_terms:                           14150
% 7.51/1.50  
% 7.51/1.50  ------ Preprocessing
% 7.51/1.50  
% 7.51/1.50  num_of_splits:                          0
% 7.51/1.50  num_of_split_atoms:                     0
% 7.51/1.50  num_of_reused_defs:                     0
% 7.51/1.50  num_eq_ax_congr_red:                    3
% 7.51/1.50  num_of_sem_filtered_clauses:            1
% 7.51/1.50  num_of_subtypes:                        3
% 7.51/1.50  monotx_restored_types:                  0
% 7.51/1.50  sat_num_of_epr_types:                   0
% 7.51/1.50  sat_num_of_non_cyclic_types:            0
% 7.51/1.50  sat_guarded_non_collapsed_types:        1
% 7.51/1.50  num_pure_diseq_elim:                    0
% 7.51/1.50  simp_replaced_by:                       0
% 7.51/1.50  res_preprocessed:                       134
% 7.51/1.50  prep_upred:                             0
% 7.51/1.50  prep_unflattend:                        7
% 7.51/1.50  smt_new_axioms:                         0
% 7.51/1.50  pred_elim_cands:                        5
% 7.51/1.50  pred_elim:                              1
% 7.51/1.50  pred_elim_cl:                           1
% 7.51/1.50  pred_elim_cycles:                       4
% 7.51/1.50  merged_defs:                            0
% 7.51/1.50  merged_defs_ncl:                        0
% 7.51/1.50  bin_hyper_res:                          0
% 7.51/1.50  prep_cycles:                            4
% 7.51/1.50  pred_elim_time:                         0.009
% 7.51/1.50  splitting_time:                         0.
% 7.51/1.50  sem_filter_time:                        0.
% 7.51/1.50  monotx_time:                            0.
% 7.51/1.50  subtype_inf_time:                       0.001
% 7.51/1.50  
% 7.51/1.50  ------ Problem properties
% 7.51/1.50  
% 7.51/1.50  clauses:                                26
% 7.51/1.50  conjectures:                            11
% 7.51/1.50  epr:                                    12
% 7.51/1.50  horn:                                   17
% 7.51/1.50  ground:                                 11
% 7.51/1.50  unary:                                  11
% 7.51/1.50  binary:                                 2
% 7.51/1.50  lits:                                   90
% 7.51/1.50  lits_eq:                                7
% 7.51/1.50  fd_pure:                                0
% 7.51/1.50  fd_pseudo:                              0
% 7.51/1.50  fd_cond:                                0
% 7.51/1.50  fd_pseudo_cond:                         1
% 7.51/1.50  ac_symbols:                             0
% 7.51/1.50  
% 7.51/1.50  ------ Propositional Solver
% 7.51/1.50  
% 7.51/1.50  prop_solver_calls:                      31
% 7.51/1.50  prop_fast_solver_calls:                 1747
% 7.51/1.50  smt_solver_calls:                       0
% 7.51/1.50  smt_fast_solver_calls:                  0
% 7.51/1.50  prop_num_of_clauses:                    6028
% 7.51/1.50  prop_preprocess_simplified:             11613
% 7.51/1.50  prop_fo_subsumed:                       176
% 7.51/1.50  prop_solver_time:                       0.
% 7.51/1.50  smt_solver_time:                        0.
% 7.51/1.50  smt_fast_solver_time:                   0.
% 7.51/1.50  prop_fast_solver_time:                  0.
% 7.51/1.50  prop_unsat_core_time:                   0.001
% 7.51/1.50  
% 7.51/1.50  ------ QBF
% 7.51/1.50  
% 7.51/1.50  qbf_q_res:                              0
% 7.51/1.50  qbf_num_tautologies:                    0
% 7.51/1.50  qbf_prep_cycles:                        0
% 7.51/1.50  
% 7.51/1.50  ------ BMC1
% 7.51/1.50  
% 7.51/1.50  bmc1_current_bound:                     -1
% 7.51/1.50  bmc1_last_solved_bound:                 -1
% 7.51/1.50  bmc1_unsat_core_size:                   -1
% 7.51/1.50  bmc1_unsat_core_parents_size:           -1
% 7.51/1.50  bmc1_merge_next_fun:                    0
% 7.51/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.51/1.50  
% 7.51/1.50  ------ Instantiation
% 7.51/1.50  
% 7.51/1.50  inst_num_of_clauses:                    1683
% 7.51/1.50  inst_num_in_passive:                    623
% 7.51/1.50  inst_num_in_active:                     812
% 7.51/1.50  inst_num_in_unprocessed:                248
% 7.51/1.50  inst_num_of_loops:                      930
% 7.51/1.50  inst_num_of_learning_restarts:          0
% 7.51/1.50  inst_num_moves_active_passive:          114
% 7.51/1.50  inst_lit_activity:                      0
% 7.51/1.50  inst_lit_activity_moves:                1
% 7.51/1.50  inst_num_tautologies:                   0
% 7.51/1.50  inst_num_prop_implied:                  0
% 7.51/1.50  inst_num_existing_simplified:           0
% 7.51/1.50  inst_num_eq_res_simplified:             0
% 7.51/1.50  inst_num_child_elim:                    0
% 7.51/1.50  inst_num_of_dismatching_blockings:      1339
% 7.51/1.50  inst_num_of_non_proper_insts:           2316
% 7.51/1.50  inst_num_of_duplicates:                 0
% 7.51/1.50  inst_inst_num_from_inst_to_res:         0
% 7.51/1.50  inst_dismatching_checking_time:         0.
% 7.51/1.50  
% 7.51/1.50  ------ Resolution
% 7.51/1.50  
% 7.51/1.50  res_num_of_clauses:                     0
% 7.51/1.50  res_num_in_passive:                     0
% 7.51/1.50  res_num_in_active:                      0
% 7.51/1.50  res_num_of_loops:                       138
% 7.51/1.50  res_forward_subset_subsumed:            86
% 7.51/1.50  res_backward_subset_subsumed:           2
% 7.51/1.50  res_forward_subsumed:                   0
% 7.51/1.50  res_backward_subsumed:                  0
% 7.51/1.50  res_forward_subsumption_resolution:     2
% 7.51/1.50  res_backward_subsumption_resolution:    0
% 7.51/1.50  res_clause_to_clause_subsumption:       1816
% 7.51/1.50  res_orphan_elimination:                 0
% 7.51/1.50  res_tautology_del:                      304
% 7.51/1.50  res_num_eq_res_simplified:              0
% 7.51/1.50  res_num_sel_changes:                    0
% 7.51/1.50  res_moves_from_active_to_pass:          0
% 7.51/1.50  
% 7.51/1.50  ------ Superposition
% 7.51/1.50  
% 7.51/1.50  sup_time_total:                         0.
% 7.51/1.50  sup_time_generating:                    0.
% 7.51/1.50  sup_time_sim_full:                      0.
% 7.51/1.50  sup_time_sim_immed:                     0.
% 7.51/1.50  
% 7.51/1.50  sup_num_of_clauses:                     476
% 7.51/1.50  sup_num_in_active:                      140
% 7.51/1.50  sup_num_in_passive:                     336
% 7.51/1.50  sup_num_of_loops:                       184
% 7.51/1.50  sup_fw_superposition:                   264
% 7.51/1.50  sup_bw_superposition:                   386
% 7.51/1.50  sup_immediate_simplified:               173
% 7.51/1.50  sup_given_eliminated:                   0
% 7.51/1.50  comparisons_done:                       0
% 7.51/1.50  comparisons_avoided:                    0
% 7.51/1.50  
% 7.51/1.50  ------ Simplifications
% 7.51/1.50  
% 7.51/1.50  
% 7.51/1.50  sim_fw_subset_subsumed:                 39
% 7.51/1.50  sim_bw_subset_subsumed:                 24
% 7.51/1.50  sim_fw_subsumed:                        35
% 7.51/1.50  sim_bw_subsumed:                        7
% 7.51/1.50  sim_fw_subsumption_res:                 4
% 7.51/1.50  sim_bw_subsumption_res:                 3
% 7.51/1.50  sim_tautology_del:                      18
% 7.51/1.50  sim_eq_tautology_del:                   12
% 7.51/1.50  sim_eq_res_simp:                        0
% 7.51/1.50  sim_fw_demodulated:                     8
% 7.51/1.50  sim_bw_demodulated:                     42
% 7.51/1.50  sim_light_normalised:                   92
% 7.51/1.50  sim_joinable_taut:                      0
% 7.51/1.50  sim_joinable_simp:                      0
% 7.51/1.50  sim_ac_normalised:                      0
% 7.51/1.50  sim_smt_subsumption:                    0
% 7.51/1.50  
%------------------------------------------------------------------------------
