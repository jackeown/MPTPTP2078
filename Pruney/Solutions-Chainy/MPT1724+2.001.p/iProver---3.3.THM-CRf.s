%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:13 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :  186 (3071 expanded)
%              Number of clauses        :  137 ( 666 expanded)
%              Number of leaves         :   10 (1150 expanded)
%              Depth                    :   32
%              Number of atoms          : 1234 (38950 expanded)
%              Number of equality atoms :  313 (6617 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal clause size      :   28 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
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
                   => ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                        & k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
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
                   => ( m1_pre_topc(X1,X2)
                     => ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                          & k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    | k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
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
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    | k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
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
    inference(flattening,[],[f12])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            | k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
          & ( r1_tsep_1(X3,X2)
            | r1_tsep_1(X2,X3) )
          & m1_pre_topc(X1,X2)
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,sK5,X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,sK5)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
        & ( r1_tsep_1(sK5,X2)
          | r1_tsep_1(X2,sK5) )
        & m1_pre_topc(X1,X2)
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                | k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
              & ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ( k2_tsep_1(X0,sK4,k1_tsep_1(X0,X3,X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
              | k2_tsep_1(X0,sK4,k1_tsep_1(X0,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
            & ( r1_tsep_1(X3,sK4)
              | r1_tsep_1(sK4,X3) )
            & m1_pre_topc(X1,sK4)
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    | k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,sK3)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
                  | k2_tsep_1(X0,X2,k1_tsep_1(X0,sK3,X3)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) )
                & ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & m1_pre_topc(sK3,X2)
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                      | k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                    & ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
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
                  ( ( k2_tsep_1(sK2,X2,k1_tsep_1(sK2,X3,X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    | k2_tsep_1(sK2,X2,k1_tsep_1(sK2,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
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

fof(f25,plain,
    ( ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
      | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) )
    & ( r1_tsep_1(sK5,sK4)
      | r1_tsep_1(sK4,sK5) )
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f13,f24,f23,f22,f21])).

fof(f54,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f58,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,
    ( r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,plain,(
    ! [X3,X1,X0,X2] :
      ( ( k2_tsep_1(X0,X2,X1) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))
        & k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) )
      | ( ~ r1_tsep_1(X2,X3)
        & ~ r1_tsep_1(X3,X2) )
      | ( r1_tsep_1(X2,X1)
        & r1_tsep_1(X1,X2) )
      | ~ sP1(X3,X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f17,plain,(
    ! [X3,X1,X0,X2] :
      ( ( k2_tsep_1(X0,X2,X1) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))
        & k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) )
      | ( ~ r1_tsep_1(X2,X3)
        & ~ r1_tsep_1(X3,X2) )
      | ( r1_tsep_1(X2,X1)
        & r1_tsep_1(X1,X2) )
      | ~ sP1(X3,X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k2_tsep_1(X2,X3,X1) = k2_tsep_1(X2,X3,k1_tsep_1(X2,X1,X0))
        & k2_tsep_1(X2,X1,X3) = k2_tsep_1(X2,k1_tsep_1(X2,X1,X0),X3) )
      | ( ~ r1_tsep_1(X3,X0)
        & ~ r1_tsep_1(X0,X3) )
      | ( r1_tsep_1(X3,X1)
        & r1_tsep_1(X1,X3) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f17])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tsep_1(X2,X1,X3) = k2_tsep_1(X2,k1_tsep_1(X2,X1,X0),X3)
      | ~ r1_tsep_1(X3,X0)
      | r1_tsep_1(X1,X3)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
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
                 => ( ~ ( ~ ( k2_tsep_1(X0,X2,X1) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))
                            & k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) )
                        & ( r1_tsep_1(X2,X3)
                          | r1_tsep_1(X3,X2) )
                        & ~ ( r1_tsep_1(X2,X1)
                            & r1_tsep_1(X1,X2) ) )
                    & ~ ( ~ ( k2_tsep_1(X0,X2,X3) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))
                            & k2_tsep_1(X0,X3,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) )
                        & ~ ( r1_tsep_1(X2,X3)
                            & r1_tsep_1(X3,X2) )
                        & ( r1_tsep_1(X2,X1)
                          | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( k2_tsep_1(X0,X2,X1) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))
                        & k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) )
                      | ( ~ r1_tsep_1(X2,X3)
                        & ~ r1_tsep_1(X3,X2) )
                      | ( r1_tsep_1(X2,X1)
                        & r1_tsep_1(X1,X2) ) )
                    & ( ( k2_tsep_1(X0,X2,X3) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))
                        & k2_tsep_1(X0,X3,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) )
                      | ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X3,X2) )
                      | ( ~ r1_tsep_1(X2,X1)
                        & ~ r1_tsep_1(X1,X2) ) ) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( k2_tsep_1(X0,X2,X1) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))
                        & k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) )
                      | ( ~ r1_tsep_1(X2,X3)
                        & ~ r1_tsep_1(X3,X2) )
                      | ( r1_tsep_1(X2,X1)
                        & r1_tsep_1(X1,X2) ) )
                    & ( ( k2_tsep_1(X0,X2,X3) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))
                        & k2_tsep_1(X0,X3,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) )
                      | ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X3,X2) )
                      | ( ~ r1_tsep_1(X2,X1)
                        & ~ r1_tsep_1(X1,X2) ) ) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f14,plain,(
    ! [X3,X1,X0,X2] :
      ( ( k2_tsep_1(X0,X2,X3) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))
        & k2_tsep_1(X0,X3,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) )
      | ( r1_tsep_1(X2,X3)
        & r1_tsep_1(X3,X2) )
      | ( ~ r1_tsep_1(X2,X1)
        & ~ r1_tsep_1(X1,X2) )
      | ~ sP0(X3,X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( sP1(X3,X1,X0,X2)
                    & sP0(X3,X1,X0,X2) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f9,f15,f14])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X3,X1,X0,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
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

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f27,plain,(
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
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
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
               => ( ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                   => m1_pre_topc(X2,X1) )
                  & ( m1_pre_topc(X2,X1)
                   => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                  & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                   => m1_pre_topc(X1,X2) )
                  & ( m1_pre_topc(X1,X2)
                   => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X2,X1)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X2,X1) )
                & ( m1_pre_topc(X1,X2)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_pre_topc(X1,X2) ) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X2,X1)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X2,X1) )
                & ( m1_pre_topc(X1,X2)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_pre_topc(X1,X2) ) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ m1_pre_topc(X2,X1)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X2)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(cnf_transformation,[],[f7])).

fof(f61,plain,
    ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f19,plain,(
    ! [X3,X1,X0,X2] :
      ( ( k2_tsep_1(X0,X2,X3) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))
        & k2_tsep_1(X0,X3,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) )
      | ( r1_tsep_1(X2,X3)
        & r1_tsep_1(X3,X2) )
      | ( ~ r1_tsep_1(X2,X1)
        & ~ r1_tsep_1(X1,X2) )
      | ~ sP0(X3,X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k2_tsep_1(X2,X3,X0) = k2_tsep_1(X2,X3,k1_tsep_1(X2,X1,X0))
        & k2_tsep_1(X2,X0,X3) = k2_tsep_1(X2,k1_tsep_1(X2,X1,X0),X3) )
      | ( r1_tsep_1(X3,X0)
        & r1_tsep_1(X0,X3) )
      | ( ~ r1_tsep_1(X3,X1)
        & ~ r1_tsep_1(X1,X3) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f19])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tsep_1(X2,X3,X0) = k2_tsep_1(X2,X3,k1_tsep_1(X2,X1,X0))
      | r1_tsep_1(X3,X0)
      | ~ r1_tsep_1(X3,X1)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X3,X1,X0,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tsep_1(X2,X3,X0) = k2_tsep_1(X2,X3,k1_tsep_1(X2,X1,X0))
      | r1_tsep_1(X3,X0)
      | ~ r1_tsep_1(X1,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tsep_1(X2,X3,X1) = k2_tsep_1(X2,X3,k1_tsep_1(X2,X1,X0))
      | ~ r1_tsep_1(X3,X0)
      | r1_tsep_1(X3,X1)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tsep_1(X2,X1,X3) = k2_tsep_1(X2,k1_tsep_1(X2,X1,X0),X3)
      | ~ r1_tsep_1(X0,X3)
      | r1_tsep_1(X3,X1)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tsep_1(X2,X3,X1) = k2_tsep_1(X2,X3,k1_tsep_1(X2,X1,X0))
      | ~ r1_tsep_1(X0,X3)
      | r1_tsep_1(X1,X3)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1519,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1818,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1519])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1521,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1816,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1521])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1523,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1814,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1523])).

cnf(c_25,negated_conjecture,
    ( r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1525,negated_conjecture,
    ( r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1812,plain,
    ( r1_tsep_1(sK5,sK4) = iProver_top
    | r1_tsep_1(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1525])).

cnf(c_7,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | ~ r1_tsep_1(X3,X0)
    | r1_tsep_1(X1,X3)
    | k2_tsep_1(X2,k1_tsep_1(X2,X1,X0),X3) = k2_tsep_1(X2,X1,X3) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_18,plain,
    ( sP1(X0,X1,X2,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_377,plain,
    ( sP1(X0,X1,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_33])).

cnf(c_378,plain,
    ( sP1(X0,X1,sK2,X2)
    | ~ m1_pre_topc(X2,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_382,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sP1(X0,X1,sK2,X2)
    | ~ m1_pre_topc(X2,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_378,c_35,c_34])).

cnf(c_383,plain,
    ( sP1(X0,X1,sK2,X2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X2,sK2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_382])).

cnf(c_703,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X2,sK2)
    | ~ r1_tsep_1(X3,X4)
    | r1_tsep_1(X5,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | X2 != X3
    | X0 != X5
    | X1 != X4
    | k2_tsep_1(X6,k1_tsep_1(X6,X5,X4),X3) = k2_tsep_1(X6,X5,X3)
    | sK2 != X6 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_383])).

cnf(c_704,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X2,sK2)
    | ~ r1_tsep_1(X0,X2)
    | r1_tsep_1(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tsep_1(sK2,k1_tsep_1(sK2,X1,X2),X0) = k2_tsep_1(sK2,X1,X0) ),
    inference(unflattening,[status(thm)],[c_703])).

cnf(c_1508,plain,
    ( ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(X1_44,sK2)
    | ~ m1_pre_topc(X2_44,sK2)
    | ~ r1_tsep_1(X0_44,X2_44)
    | r1_tsep_1(X1_44,X0_44)
    | v2_struct_0(X0_44)
    | v2_struct_0(X1_44)
    | v2_struct_0(X2_44)
    | k2_tsep_1(sK2,k1_tsep_1(sK2,X1_44,X2_44),X0_44) = k2_tsep_1(sK2,X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_704])).

cnf(c_1829,plain,
    ( k2_tsep_1(sK2,k1_tsep_1(sK2,X0_44,X1_44),X2_44) = k2_tsep_1(sK2,X0_44,X2_44)
    | m1_pre_topc(X1_44,sK2) != iProver_top
    | m1_pre_topc(X0_44,sK2) != iProver_top
    | m1_pre_topc(X2_44,sK2) != iProver_top
    | r1_tsep_1(X2_44,X1_44) != iProver_top
    | r1_tsep_1(X0_44,X2_44) = iProver_top
    | v2_struct_0(X0_44) = iProver_top
    | v2_struct_0(X2_44) = iProver_top
    | v2_struct_0(X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1508])).

cnf(c_4463,plain,
    ( k2_tsep_1(sK2,k1_tsep_1(sK2,X0_44,sK4),sK5) = k2_tsep_1(sK2,X0_44,sK5)
    | m1_pre_topc(X0_44,sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | r1_tsep_1(X0_44,sK5) = iProver_top
    | r1_tsep_1(sK4,sK5) = iProver_top
    | v2_struct_0(X0_44) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1812,c_1829])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_39,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_40,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_41,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_42,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_43,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_44,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_45,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tsep_1(X1,X0)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_440,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tsep_1(X2,X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_33])).

cnf(c_441,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ r1_tsep_1(X1,X0)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_443,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ r1_tsep_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_441,c_35,c_34])).

cnf(c_444,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ r1_tsep_1(X1,X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_443])).

cnf(c_1515,plain,
    ( ~ m1_pre_topc(X0_44,X1_44)
    | ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(X1_44,sK2)
    | ~ r1_tsep_1(X1_44,X0_44)
    | v2_struct_0(X0_44)
    | v2_struct_0(X1_44) ),
    inference(subtyping,[status(esa)],[c_444])).

cnf(c_2307,plain,
    ( ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(sK3,X0_44)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ r1_tsep_1(X0_44,sK3)
    | v2_struct_0(X0_44)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1515])).

cnf(c_2508,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ r1_tsep_1(sK4,sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2307])).

cnf(c_2509,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | r1_tsep_1(sK4,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2508])).

cnf(c_1524,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1813,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1524])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tsep_1(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_525,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | r1_tsep_1(X1,X0)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(X2,X1,X0)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_526,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | r1_tsep_1(X1,X0)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK2,X1,X0) ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_529,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X0,X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK2,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_526,c_35,c_34,c_444])).

cnf(c_530,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK2,X1,X0) ),
    inference(renaming,[status(thm)],[c_529])).

cnf(c_1512,plain,
    ( ~ m1_pre_topc(X0_44,X1_44)
    | ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(X1_44,sK2)
    | v2_struct_0(X0_44)
    | v2_struct_0(X1_44)
    | g1_pre_topc(u1_struct_0(X0_44),u1_pre_topc(X0_44)) = k2_tsep_1(sK2,X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_530])).

cnf(c_1825,plain,
    ( g1_pre_topc(u1_struct_0(X0_44),u1_pre_topc(X0_44)) = k2_tsep_1(sK2,X1_44,X0_44)
    | m1_pre_topc(X0_44,X1_44) != iProver_top
    | m1_pre_topc(X1_44,sK2) != iProver_top
    | m1_pre_topc(X0_44,sK2) != iProver_top
    | v2_struct_0(X1_44) = iProver_top
    | v2_struct_0(X0_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1512])).

cnf(c_3892,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK4,sK3)
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1813,c_1825])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | r1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(X2,X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_161,plain,
    ( ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(X2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_1])).

cnf(c_162,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(X1,X0,X2) ),
    inference(renaming,[status(thm)],[c_161])).

cnf(c_466,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(X2,X0,X1)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_162,c_33])).

cnf(c_467,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_471,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_467,c_35,c_34])).

cnf(c_472,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK2,X0,X1) ),
    inference(renaming,[status(thm)],[c_471])).

cnf(c_1514,plain,
    ( ~ m1_pre_topc(X0_44,X1_44)
    | ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(X1_44,sK2)
    | v2_struct_0(X0_44)
    | v2_struct_0(X1_44)
    | g1_pre_topc(u1_struct_0(X0_44),u1_pre_topc(X0_44)) = k2_tsep_1(sK2,X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_472])).

cnf(c_1823,plain,
    ( g1_pre_topc(u1_struct_0(X0_44),u1_pre_topc(X0_44)) = k2_tsep_1(sK2,X0_44,X1_44)
    | m1_pre_topc(X0_44,X1_44) != iProver_top
    | m1_pre_topc(X1_44,sK2) != iProver_top
    | m1_pre_topc(X0_44,sK2) != iProver_top
    | v2_struct_0(X1_44) = iProver_top
    | v2_struct_0(X0_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1514])).

cnf(c_3416,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK3,sK4)
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1813,c_1823])).

cnf(c_2352,plain,
    ( ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(sK3,X0_44)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(X0_44)
    | v2_struct_0(sK3)
    | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK3,X0_44) ),
    inference(instantiation,[status(thm)],[c_1514])).

cnf(c_2585,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2352])).

cnf(c_3686,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3416,c_32,c_31,c_30,c_29,c_26,c_2585])).

cnf(c_3932,plain,
    ( k2_tsep_1(sK2,sK4,sK3) = k2_tsep_1(sK2,sK3,sK4)
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3892,c_3686])).

cnf(c_4028,plain,
    ( k2_tsep_1(sK2,sK4,sK3) = k2_tsep_1(sK2,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3932,c_39,c_40,c_41,c_42])).

cnf(c_24,negated_conjecture,
    ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1526,negated_conjecture,
    ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_3689,plain,
    ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) != k2_tsep_1(sK2,sK3,sK4)
    | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) != k2_tsep_1(sK2,sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_3686,c_1526])).

cnf(c_4033,plain,
    ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) != k2_tsep_1(sK2,sK4,sK3)
    | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) != k2_tsep_1(sK2,sK4,sK3) ),
    inference(demodulation,[status(thm)],[c_4028,c_3689])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_tsep_1(X3,X1)
    | r1_tsep_1(X3,X0)
    | k2_tsep_1(X2,X3,k1_tsep_1(X2,X1,X0)) = k2_tsep_1(X2,X3,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_19,plain,
    ( sP0(X0,X1,X2,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_344,plain,
    ( sP0(X0,X1,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_33])).

cnf(c_345,plain,
    ( sP0(X0,X1,sK2,X2)
    | ~ m1_pre_topc(X2,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_349,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sP0(X0,X1,sK2,X2)
    | ~ m1_pre_topc(X2,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_345,c_35,c_34])).

cnf(c_350,plain,
    ( sP0(X0,X1,sK2,X2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X2,sK2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_349])).

cnf(c_1186,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X2,sK2)
    | ~ r1_tsep_1(X3,X4)
    | r1_tsep_1(X3,X5)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | X2 != X3
    | X0 != X4
    | X1 != X5
    | k2_tsep_1(X6,X3,k1_tsep_1(X6,X4,X5)) = k2_tsep_1(X6,X3,X5)
    | sK2 != X6 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_350])).

cnf(c_1187,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X2,sK2)
    | ~ r1_tsep_1(X0,X2)
    | r1_tsep_1(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tsep_1(sK2,X0,k1_tsep_1(sK2,X2,X1)) = k2_tsep_1(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_1186])).

cnf(c_1495,plain,
    ( ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(X1_44,sK2)
    | ~ m1_pre_topc(X2_44,sK2)
    | ~ r1_tsep_1(X0_44,X2_44)
    | r1_tsep_1(X0_44,X1_44)
    | v2_struct_0(X0_44)
    | v2_struct_0(X1_44)
    | v2_struct_0(X2_44)
    | k2_tsep_1(sK2,X0_44,k1_tsep_1(sK2,X2_44,X1_44)) = k2_tsep_1(sK2,X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_1187])).

cnf(c_2378,plain,
    ( ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(X1_44,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ r1_tsep_1(sK4,X1_44)
    | r1_tsep_1(sK4,X0_44)
    | v2_struct_0(X0_44)
    | v2_struct_0(X1_44)
    | v2_struct_0(sK4)
    | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,X1_44,X0_44)) = k2_tsep_1(sK2,sK4,X0_44) ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_2622,plain,
    ( ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ r1_tsep_1(sK4,X0_44)
    | r1_tsep_1(sK4,sK3)
    | v2_struct_0(X0_44)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,X0_44,sK3)) = k2_tsep_1(sK2,sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_2378])).

cnf(c_3181,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | r1_tsep_1(sK4,sK3)
    | ~ r1_tsep_1(sK4,sK5)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) = k2_tsep_1(sK2,sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_2622])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_tsep_1(X1,X3)
    | r1_tsep_1(X3,X0)
    | k2_tsep_1(X2,X3,k1_tsep_1(X2,X1,X0)) = k2_tsep_1(X2,X3,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1155,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X2,sK2)
    | ~ r1_tsep_1(X3,X4)
    | r1_tsep_1(X4,X5)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | X2 != X4
    | X0 != X3
    | X1 != X5
    | k2_tsep_1(X6,X4,k1_tsep_1(X6,X3,X5)) = k2_tsep_1(X6,X4,X5)
    | sK2 != X6 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_350])).

cnf(c_1156,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X2,sK2)
    | ~ r1_tsep_1(X0,X2)
    | r1_tsep_1(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tsep_1(sK2,X2,k1_tsep_1(sK2,X0,X1)) = k2_tsep_1(sK2,X2,X1) ),
    inference(unflattening,[status(thm)],[c_1155])).

cnf(c_1496,plain,
    ( ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(X1_44,sK2)
    | ~ m1_pre_topc(X2_44,sK2)
    | ~ r1_tsep_1(X0_44,X2_44)
    | r1_tsep_1(X2_44,X1_44)
    | v2_struct_0(X0_44)
    | v2_struct_0(X1_44)
    | v2_struct_0(X2_44)
    | k2_tsep_1(sK2,X2_44,k1_tsep_1(sK2,X0_44,X1_44)) = k2_tsep_1(sK2,X2_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_1156])).

cnf(c_2384,plain,
    ( ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(X1_44,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | r1_tsep_1(X1_44,X0_44)
    | ~ r1_tsep_1(sK5,X1_44)
    | v2_struct_0(X0_44)
    | v2_struct_0(X1_44)
    | v2_struct_0(sK5)
    | k2_tsep_1(sK2,X1_44,k1_tsep_1(sK2,sK5,X0_44)) = k2_tsep_1(sK2,X1_44,X0_44) ),
    inference(instantiation,[status(thm)],[c_1496])).

cnf(c_2743,plain,
    ( ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | r1_tsep_1(X0_44,sK3)
    | ~ r1_tsep_1(sK5,X0_44)
    | v2_struct_0(X0_44)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | k2_tsep_1(sK2,X0_44,k1_tsep_1(sK2,sK5,sK3)) = k2_tsep_1(sK2,X0_44,sK3) ),
    inference(instantiation,[status(thm)],[c_2384])).

cnf(c_3537,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK4,sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) = k2_tsep_1(sK2,sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_2743])).

cnf(c_4057,plain,
    ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) != k2_tsep_1(sK2,sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4033,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_25,c_2508,c_3181,c_3537])).

cnf(c_2,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | ~ r1_tsep_1(X3,X0)
    | r1_tsep_1(X3,X1)
    | k2_tsep_1(X2,X3,k1_tsep_1(X2,X1,X0)) = k2_tsep_1(X2,X3,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_858,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X2,sK2)
    | ~ r1_tsep_1(X3,X4)
    | r1_tsep_1(X3,X5)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | X2 != X3
    | X0 != X5
    | X1 != X4
    | k2_tsep_1(X6,X3,k1_tsep_1(X6,X5,X4)) = k2_tsep_1(X6,X3,X5)
    | sK2 != X6 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_383])).

cnf(c_859,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X2,sK2)
    | ~ r1_tsep_1(X0,X2)
    | r1_tsep_1(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tsep_1(sK2,X0,k1_tsep_1(sK2,X1,X2)) = k2_tsep_1(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_858])).

cnf(c_1503,plain,
    ( ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(X1_44,sK2)
    | ~ m1_pre_topc(X2_44,sK2)
    | ~ r1_tsep_1(X0_44,X2_44)
    | r1_tsep_1(X0_44,X1_44)
    | v2_struct_0(X0_44)
    | v2_struct_0(X1_44)
    | v2_struct_0(X2_44)
    | k2_tsep_1(sK2,X0_44,k1_tsep_1(sK2,X1_44,X2_44)) = k2_tsep_1(sK2,X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_859])).

cnf(c_3104,plain,
    ( ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(X1_44,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ r1_tsep_1(sK4,X1_44)
    | r1_tsep_1(sK4,X0_44)
    | v2_struct_0(X0_44)
    | v2_struct_0(X1_44)
    | v2_struct_0(sK4)
    | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,X0_44,X1_44)) = k2_tsep_1(sK2,sK4,X0_44) ),
    inference(instantiation,[status(thm)],[c_1503])).

cnf(c_4009,plain,
    ( ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ r1_tsep_1(sK4,X0_44)
    | r1_tsep_1(sK4,sK3)
    | v2_struct_0(X0_44)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,X0_44)) = k2_tsep_1(sK2,sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_3104])).

cnf(c_4412,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | r1_tsep_1(sK4,sK3)
    | ~ r1_tsep_1(sK4,sK5)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) = k2_tsep_1(sK2,sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_4009])).

cnf(c_4413,plain,
    ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) = k2_tsep_1(sK2,sK4,sK3)
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | r1_tsep_1(sK4,sK3) = iProver_top
    | r1_tsep_1(sK4,sK5) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4412])).

cnf(c_4647,plain,
    ( r1_tsep_1(X0_44,sK5) = iProver_top
    | m1_pre_topc(X0_44,sK2) != iProver_top
    | k2_tsep_1(sK2,k1_tsep_1(sK2,X0_44,sK4),sK5) = k2_tsep_1(sK2,X0_44,sK5)
    | v2_struct_0(X0_44) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4463,c_32,c_39,c_31,c_40,c_30,c_41,c_29,c_42,c_28,c_43,c_27,c_44,c_26,c_45,c_25,c_2508,c_2509,c_3181,c_3537,c_4033,c_4413])).

cnf(c_4648,plain,
    ( k2_tsep_1(sK2,k1_tsep_1(sK2,X0_44,sK4),sK5) = k2_tsep_1(sK2,X0_44,sK5)
    | m1_pre_topc(X0_44,sK2) != iProver_top
    | r1_tsep_1(X0_44,sK5) = iProver_top
    | v2_struct_0(X0_44) = iProver_top ),
    inference(renaming,[status(thm)],[c_4647])).

cnf(c_4657,plain,
    ( k2_tsep_1(sK2,k1_tsep_1(sK2,sK5,sK4),sK5) = k2_tsep_1(sK2,sK5,sK5)
    | r1_tsep_1(sK5,sK5) = iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1814,c_4648])).

cnf(c_4682,plain,
    ( r1_tsep_1(sK5,sK5) = iProver_top
    | k2_tsep_1(sK2,k1_tsep_1(sK2,sK5,sK4),sK5) = k2_tsep_1(sK2,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4657,c_43])).

cnf(c_4683,plain,
    ( k2_tsep_1(sK2,k1_tsep_1(sK2,sK5,sK4),sK5) = k2_tsep_1(sK2,sK5,sK5)
    | r1_tsep_1(sK5,sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_4682])).

cnf(c_8,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | ~ r1_tsep_1(X0,X3)
    | r1_tsep_1(X3,X1)
    | k2_tsep_1(X2,k1_tsep_1(X2,X1,X0),X3) = k2_tsep_1(X2,X1,X3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_672,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X2,sK2)
    | ~ r1_tsep_1(X3,X4)
    | r1_tsep_1(X4,X5)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | X2 != X4
    | X0 != X5
    | X1 != X3
    | k2_tsep_1(X6,k1_tsep_1(X6,X5,X3),X4) = k2_tsep_1(X6,X5,X4)
    | sK2 != X6 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_383])).

cnf(c_673,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X2,sK2)
    | ~ r1_tsep_1(X0,X2)
    | r1_tsep_1(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tsep_1(sK2,k1_tsep_1(sK2,X1,X0),X2) = k2_tsep_1(sK2,X1,X2) ),
    inference(unflattening,[status(thm)],[c_672])).

cnf(c_1509,plain,
    ( ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(X1_44,sK2)
    | ~ m1_pre_topc(X2_44,sK2)
    | ~ r1_tsep_1(X0_44,X2_44)
    | r1_tsep_1(X2_44,X1_44)
    | v2_struct_0(X0_44)
    | v2_struct_0(X1_44)
    | v2_struct_0(X2_44)
    | k2_tsep_1(sK2,k1_tsep_1(sK2,X1_44,X0_44),X2_44) = k2_tsep_1(sK2,X1_44,X2_44) ),
    inference(subtyping,[status(esa)],[c_673])).

cnf(c_1828,plain,
    ( k2_tsep_1(sK2,k1_tsep_1(sK2,X0_44,X1_44),X2_44) = k2_tsep_1(sK2,X0_44,X2_44)
    | m1_pre_topc(X2_44,sK2) != iProver_top
    | m1_pre_topc(X0_44,sK2) != iProver_top
    | m1_pre_topc(X1_44,sK2) != iProver_top
    | r1_tsep_1(X1_44,X2_44) != iProver_top
    | r1_tsep_1(X2_44,X0_44) = iProver_top
    | v2_struct_0(X0_44) = iProver_top
    | v2_struct_0(X1_44) = iProver_top
    | v2_struct_0(X2_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1509])).

cnf(c_4689,plain,
    ( k2_tsep_1(sK2,k1_tsep_1(sK2,X0_44,sK5),sK5) = k2_tsep_1(sK2,X0_44,sK5)
    | k2_tsep_1(sK2,k1_tsep_1(sK2,sK5,sK4),sK5) = k2_tsep_1(sK2,sK5,sK5)
    | m1_pre_topc(X0_44,sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | r1_tsep_1(sK5,X0_44) = iProver_top
    | v2_struct_0(X0_44) = iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4683,c_1828])).

cnf(c_5006,plain,
    ( v2_struct_0(X0_44) = iProver_top
    | r1_tsep_1(sK5,X0_44) = iProver_top
    | k2_tsep_1(sK2,k1_tsep_1(sK2,X0_44,sK5),sK5) = k2_tsep_1(sK2,X0_44,sK5)
    | k2_tsep_1(sK2,k1_tsep_1(sK2,sK5,sK4),sK5) = k2_tsep_1(sK2,sK5,sK5)
    | m1_pre_topc(X0_44,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4689,c_43,c_44])).

cnf(c_5007,plain,
    ( k2_tsep_1(sK2,k1_tsep_1(sK2,X0_44,sK5),sK5) = k2_tsep_1(sK2,X0_44,sK5)
    | k2_tsep_1(sK2,k1_tsep_1(sK2,sK5,sK4),sK5) = k2_tsep_1(sK2,sK5,sK5)
    | m1_pre_topc(X0_44,sK2) != iProver_top
    | r1_tsep_1(sK5,X0_44) = iProver_top
    | v2_struct_0(X0_44) = iProver_top ),
    inference(renaming,[status(thm)],[c_5006])).

cnf(c_5018,plain,
    ( k2_tsep_1(sK2,k1_tsep_1(sK2,sK5,sK4),sK5) = k2_tsep_1(sK2,sK5,sK5)
    | k2_tsep_1(sK2,k1_tsep_1(sK2,sK4,sK5),sK5) = k2_tsep_1(sK2,sK4,sK5)
    | r1_tsep_1(sK5,sK4) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1816,c_5007])).

cnf(c_46,plain,
    ( r1_tsep_1(sK5,sK4) = iProver_top
    | r1_tsep_1(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5039,plain,
    ( r1_tsep_1(sK5,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5018,c_32,c_39,c_31,c_40,c_30,c_41,c_29,c_42,c_28,c_43,c_27,c_44,c_26,c_45,c_25,c_46,c_2508,c_2509,c_3181,c_3537,c_4033,c_4413])).

cnf(c_5,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | ~ r1_tsep_1(X0,X3)
    | r1_tsep_1(X1,X3)
    | k2_tsep_1(X2,X3,k1_tsep_1(X2,X1,X0)) = k2_tsep_1(X2,X3,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_765,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X2,sK2)
    | ~ r1_tsep_1(X3,X4)
    | r1_tsep_1(X5,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | X2 != X4
    | X0 != X5
    | X1 != X3
    | k2_tsep_1(X6,X4,k1_tsep_1(X6,X5,X3)) = k2_tsep_1(X6,X4,X5)
    | sK2 != X6 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_383])).

cnf(c_766,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X2,sK2)
    | ~ r1_tsep_1(X0,X2)
    | r1_tsep_1(X1,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tsep_1(sK2,X2,k1_tsep_1(sK2,X1,X0)) = k2_tsep_1(sK2,X2,X1) ),
    inference(unflattening,[status(thm)],[c_765])).

cnf(c_1506,plain,
    ( ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(X1_44,sK2)
    | ~ m1_pre_topc(X2_44,sK2)
    | ~ r1_tsep_1(X0_44,X2_44)
    | r1_tsep_1(X1_44,X2_44)
    | v2_struct_0(X0_44)
    | v2_struct_0(X1_44)
    | v2_struct_0(X2_44)
    | k2_tsep_1(sK2,X2_44,k1_tsep_1(sK2,X1_44,X0_44)) = k2_tsep_1(sK2,X2_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_766])).

cnf(c_1831,plain,
    ( k2_tsep_1(sK2,X0_44,k1_tsep_1(sK2,X1_44,X2_44)) = k2_tsep_1(sK2,X0_44,X1_44)
    | m1_pre_topc(X0_44,sK2) != iProver_top
    | m1_pre_topc(X1_44,sK2) != iProver_top
    | m1_pre_topc(X2_44,sK2) != iProver_top
    | r1_tsep_1(X2_44,X0_44) != iProver_top
    | r1_tsep_1(X1_44,X0_44) = iProver_top
    | v2_struct_0(X1_44) = iProver_top
    | v2_struct_0(X2_44) = iProver_top
    | v2_struct_0(X0_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1506])).

cnf(c_5570,plain,
    ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,X0_44,sK5)) = k2_tsep_1(sK2,sK4,X0_44)
    | m1_pre_topc(X0_44,sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | r1_tsep_1(X0_44,sK4) = iProver_top
    | v2_struct_0(X0_44) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5039,c_1831])).

cnf(c_6075,plain,
    ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,X0_44,sK5)) = k2_tsep_1(sK2,sK4,X0_44)
    | m1_pre_topc(X0_44,sK2) != iProver_top
    | r1_tsep_1(X0_44,sK4) = iProver_top
    | v2_struct_0(X0_44) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5570,c_41,c_42,c_43,c_44])).

cnf(c_6087,plain,
    ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) = k2_tsep_1(sK2,sK4,sK3)
    | r1_tsep_1(sK3,sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1818,c_6075])).

cnf(c_410,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tsep_1(X0,X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_33])).

cnf(c_411,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ r1_tsep_1(X0,X1)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_415,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ r1_tsep_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_411,c_35,c_34])).

cnf(c_416,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ r1_tsep_1(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_415])).

cnf(c_1516,plain,
    ( ~ m1_pre_topc(X0_44,X1_44)
    | ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(X1_44,sK2)
    | ~ r1_tsep_1(X0_44,X1_44)
    | v2_struct_0(X0_44)
    | v2_struct_0(X1_44) ),
    inference(subtyping,[status(esa)],[c_416])).

cnf(c_2322,plain,
    ( ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(sK3,X0_44)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ r1_tsep_1(sK3,X0_44)
    | v2_struct_0(X0_44)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1516])).

cnf(c_2533,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ r1_tsep_1(sK3,sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2322])).

cnf(c_2534,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | r1_tsep_1(sK3,sK4) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2533])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6087,c_4057,c_2534,c_45,c_42,c_41,c_40,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:25:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 2.37/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/0.98  
% 2.37/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.37/0.98  
% 2.37/0.98  ------  iProver source info
% 2.37/0.98  
% 2.37/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.37/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.37/0.98  git: non_committed_changes: false
% 2.37/0.98  git: last_make_outside_of_git: false
% 2.37/0.98  
% 2.37/0.98  ------ 
% 2.37/0.98  
% 2.37/0.98  ------ Input Options
% 2.37/0.98  
% 2.37/0.98  --out_options                           all
% 2.37/0.98  --tptp_safe_out                         true
% 2.37/0.98  --problem_path                          ""
% 2.37/0.98  --include_path                          ""
% 2.37/0.98  --clausifier                            res/vclausify_rel
% 2.37/0.98  --clausifier_options                    --mode clausify
% 2.37/0.98  --stdin                                 false
% 2.37/0.98  --stats_out                             all
% 2.37/0.98  
% 2.37/0.98  ------ General Options
% 2.37/0.98  
% 2.37/0.98  --fof                                   false
% 2.37/0.98  --time_out_real                         305.
% 2.37/0.98  --time_out_virtual                      -1.
% 2.37/0.98  --symbol_type_check                     false
% 2.37/0.98  --clausify_out                          false
% 2.37/0.98  --sig_cnt_out                           false
% 2.37/0.98  --trig_cnt_out                          false
% 2.37/0.98  --trig_cnt_out_tolerance                1.
% 2.37/0.98  --trig_cnt_out_sk_spl                   false
% 2.37/0.98  --abstr_cl_out                          false
% 2.37/0.98  
% 2.37/0.98  ------ Global Options
% 2.37/0.98  
% 2.37/0.98  --schedule                              default
% 2.37/0.98  --add_important_lit                     false
% 2.37/0.98  --prop_solver_per_cl                    1000
% 2.37/0.98  --min_unsat_core                        false
% 2.37/0.98  --soft_assumptions                      false
% 2.37/0.98  --soft_lemma_size                       3
% 2.37/0.98  --prop_impl_unit_size                   0
% 2.37/0.98  --prop_impl_unit                        []
% 2.37/0.98  --share_sel_clauses                     true
% 2.37/0.98  --reset_solvers                         false
% 2.37/0.98  --bc_imp_inh                            [conj_cone]
% 2.37/0.98  --conj_cone_tolerance                   3.
% 2.37/0.98  --extra_neg_conj                        none
% 2.37/0.98  --large_theory_mode                     true
% 2.37/0.98  --prolific_symb_bound                   200
% 2.37/0.98  --lt_threshold                          2000
% 2.37/0.98  --clause_weak_htbl                      true
% 2.37/0.98  --gc_record_bc_elim                     false
% 2.37/0.98  
% 2.37/0.98  ------ Preprocessing Options
% 2.37/0.98  
% 2.37/0.98  --preprocessing_flag                    true
% 2.37/0.98  --time_out_prep_mult                    0.1
% 2.37/0.98  --splitting_mode                        input
% 2.37/0.98  --splitting_grd                         true
% 2.37/0.98  --splitting_cvd                         false
% 2.37/0.98  --splitting_cvd_svl                     false
% 2.37/0.98  --splitting_nvd                         32
% 2.37/0.98  --sub_typing                            true
% 2.37/0.98  --prep_gs_sim                           true
% 2.37/0.98  --prep_unflatten                        true
% 2.37/0.98  --prep_res_sim                          true
% 2.37/0.98  --prep_upred                            true
% 2.37/0.98  --prep_sem_filter                       exhaustive
% 2.37/0.98  --prep_sem_filter_out                   false
% 2.37/0.98  --pred_elim                             true
% 2.37/0.98  --res_sim_input                         true
% 2.37/0.98  --eq_ax_congr_red                       true
% 2.37/0.98  --pure_diseq_elim                       true
% 2.37/0.98  --brand_transform                       false
% 2.37/0.98  --non_eq_to_eq                          false
% 2.37/0.98  --prep_def_merge                        true
% 2.37/0.98  --prep_def_merge_prop_impl              false
% 2.37/0.98  --prep_def_merge_mbd                    true
% 2.37/0.98  --prep_def_merge_tr_red                 false
% 2.37/0.98  --prep_def_merge_tr_cl                  false
% 2.37/0.98  --smt_preprocessing                     true
% 2.37/0.98  --smt_ac_axioms                         fast
% 2.37/0.98  --preprocessed_out                      false
% 2.37/0.98  --preprocessed_stats                    false
% 2.37/0.98  
% 2.37/0.98  ------ Abstraction refinement Options
% 2.37/0.98  
% 2.37/0.98  --abstr_ref                             []
% 2.37/0.98  --abstr_ref_prep                        false
% 2.37/0.98  --abstr_ref_until_sat                   false
% 2.37/0.98  --abstr_ref_sig_restrict                funpre
% 2.37/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.37/0.98  --abstr_ref_under                       []
% 2.37/0.98  
% 2.37/0.98  ------ SAT Options
% 2.37/0.98  
% 2.37/0.98  --sat_mode                              false
% 2.37/0.98  --sat_fm_restart_options                ""
% 2.37/0.98  --sat_gr_def                            false
% 2.37/0.98  --sat_epr_types                         true
% 2.37/0.98  --sat_non_cyclic_types                  false
% 2.37/0.98  --sat_finite_models                     false
% 2.37/0.98  --sat_fm_lemmas                         false
% 2.37/0.98  --sat_fm_prep                           false
% 2.37/0.98  --sat_fm_uc_incr                        true
% 2.37/0.98  --sat_out_model                         small
% 2.37/0.98  --sat_out_clauses                       false
% 2.37/0.98  
% 2.37/0.98  ------ QBF Options
% 2.37/0.98  
% 2.37/0.98  --qbf_mode                              false
% 2.37/0.98  --qbf_elim_univ                         false
% 2.37/0.98  --qbf_dom_inst                          none
% 2.37/0.98  --qbf_dom_pre_inst                      false
% 2.37/0.98  --qbf_sk_in                             false
% 2.37/0.98  --qbf_pred_elim                         true
% 2.37/0.98  --qbf_split                             512
% 2.37/0.98  
% 2.37/0.98  ------ BMC1 Options
% 2.37/0.98  
% 2.37/0.98  --bmc1_incremental                      false
% 2.37/0.98  --bmc1_axioms                           reachable_all
% 2.37/0.98  --bmc1_min_bound                        0
% 2.37/0.98  --bmc1_max_bound                        -1
% 2.37/0.98  --bmc1_max_bound_default                -1
% 2.37/0.98  --bmc1_symbol_reachability              true
% 2.37/0.98  --bmc1_property_lemmas                  false
% 2.37/0.98  --bmc1_k_induction                      false
% 2.37/0.98  --bmc1_non_equiv_states                 false
% 2.37/0.98  --bmc1_deadlock                         false
% 2.37/0.98  --bmc1_ucm                              false
% 2.37/0.98  --bmc1_add_unsat_core                   none
% 2.37/0.98  --bmc1_unsat_core_children              false
% 2.37/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.37/0.98  --bmc1_out_stat                         full
% 2.37/0.98  --bmc1_ground_init                      false
% 2.37/0.98  --bmc1_pre_inst_next_state              false
% 2.37/0.98  --bmc1_pre_inst_state                   false
% 2.37/0.98  --bmc1_pre_inst_reach_state             false
% 2.37/0.98  --bmc1_out_unsat_core                   false
% 2.37/0.98  --bmc1_aig_witness_out                  false
% 2.37/0.98  --bmc1_verbose                          false
% 2.37/0.98  --bmc1_dump_clauses_tptp                false
% 2.37/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.37/0.98  --bmc1_dump_file                        -
% 2.37/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.37/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.37/0.98  --bmc1_ucm_extend_mode                  1
% 2.37/0.98  --bmc1_ucm_init_mode                    2
% 2.37/0.98  --bmc1_ucm_cone_mode                    none
% 2.37/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.37/0.98  --bmc1_ucm_relax_model                  4
% 2.37/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.37/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.37/0.98  --bmc1_ucm_layered_model                none
% 2.37/0.98  --bmc1_ucm_max_lemma_size               10
% 2.37/0.98  
% 2.37/0.98  ------ AIG Options
% 2.37/0.98  
% 2.37/0.98  --aig_mode                              false
% 2.37/0.98  
% 2.37/0.98  ------ Instantiation Options
% 2.37/0.98  
% 2.37/0.98  --instantiation_flag                    true
% 2.37/0.98  --inst_sos_flag                         false
% 2.37/0.98  --inst_sos_phase                        true
% 2.37/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.37/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.37/0.98  --inst_lit_sel_side                     num_symb
% 2.37/0.98  --inst_solver_per_active                1400
% 2.37/0.98  --inst_solver_calls_frac                1.
% 2.37/0.98  --inst_passive_queue_type               priority_queues
% 2.37/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.37/0.98  --inst_passive_queues_freq              [25;2]
% 2.37/0.98  --inst_dismatching                      true
% 2.37/0.98  --inst_eager_unprocessed_to_passive     true
% 2.37/0.98  --inst_prop_sim_given                   true
% 2.37/0.98  --inst_prop_sim_new                     false
% 2.37/0.98  --inst_subs_new                         false
% 2.37/0.98  --inst_eq_res_simp                      false
% 2.37/0.98  --inst_subs_given                       false
% 2.37/0.98  --inst_orphan_elimination               true
% 2.37/0.98  --inst_learning_loop_flag               true
% 2.37/0.98  --inst_learning_start                   3000
% 2.37/0.98  --inst_learning_factor                  2
% 2.37/0.98  --inst_start_prop_sim_after_learn       3
% 2.37/0.98  --inst_sel_renew                        solver
% 2.37/0.98  --inst_lit_activity_flag                true
% 2.37/0.98  --inst_restr_to_given                   false
% 2.37/0.98  --inst_activity_threshold               500
% 2.37/0.98  --inst_out_proof                        true
% 2.37/0.98  
% 2.37/0.98  ------ Resolution Options
% 2.37/0.98  
% 2.37/0.98  --resolution_flag                       true
% 2.37/0.98  --res_lit_sel                           adaptive
% 2.37/0.98  --res_lit_sel_side                      none
% 2.37/0.98  --res_ordering                          kbo
% 2.37/0.98  --res_to_prop_solver                    active
% 2.37/0.98  --res_prop_simpl_new                    false
% 2.37/0.98  --res_prop_simpl_given                  true
% 2.37/0.98  --res_passive_queue_type                priority_queues
% 2.37/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.37/0.98  --res_passive_queues_freq               [15;5]
% 2.37/0.98  --res_forward_subs                      full
% 2.37/0.98  --res_backward_subs                     full
% 2.37/0.98  --res_forward_subs_resolution           true
% 2.37/0.98  --res_backward_subs_resolution          true
% 2.37/0.98  --res_orphan_elimination                true
% 2.37/0.98  --res_time_limit                        2.
% 2.37/0.98  --res_out_proof                         true
% 2.37/0.98  
% 2.37/0.98  ------ Superposition Options
% 2.37/0.98  
% 2.37/0.98  --superposition_flag                    true
% 2.37/0.98  --sup_passive_queue_type                priority_queues
% 2.37/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.37/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.37/0.98  --demod_completeness_check              fast
% 2.37/0.98  --demod_use_ground                      true
% 2.37/0.98  --sup_to_prop_solver                    passive
% 2.37/0.98  --sup_prop_simpl_new                    true
% 2.37/0.98  --sup_prop_simpl_given                  true
% 2.37/0.98  --sup_fun_splitting                     false
% 2.37/0.98  --sup_smt_interval                      50000
% 2.37/0.98  
% 2.37/0.98  ------ Superposition Simplification Setup
% 2.37/0.98  
% 2.37/0.98  --sup_indices_passive                   []
% 2.37/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.37/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/0.98  --sup_full_bw                           [BwDemod]
% 2.37/0.98  --sup_immed_triv                        [TrivRules]
% 2.37/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.37/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/0.98  --sup_immed_bw_main                     []
% 2.37/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.37/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/0.98  
% 2.37/0.98  ------ Combination Options
% 2.37/0.98  
% 2.37/0.98  --comb_res_mult                         3
% 2.37/0.98  --comb_sup_mult                         2
% 2.37/0.98  --comb_inst_mult                        10
% 2.37/0.98  
% 2.37/0.98  ------ Debug Options
% 2.37/0.98  
% 2.37/0.98  --dbg_backtrace                         false
% 2.37/0.98  --dbg_dump_prop_clauses                 false
% 2.37/0.98  --dbg_dump_prop_clauses_file            -
% 2.37/0.98  --dbg_out_stat                          false
% 2.37/0.98  ------ Parsing...
% 2.37/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.37/0.98  
% 2.37/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.37/0.98  
% 2.37/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.37/0.98  
% 2.37/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.37/0.98  ------ Proving...
% 2.37/0.98  ------ Problem Properties 
% 2.37/0.98  
% 2.37/0.98  
% 2.37/0.98  clauses                                 32
% 2.37/0.98  conjectures                             10
% 2.37/0.98  EPR                                     11
% 2.37/0.98  Horn                                    9
% 2.37/0.98  unary                                   8
% 2.37/0.98  binary                                  2
% 2.37/0.98  lits                                    194
% 2.37/0.98  lits eq                                 22
% 2.37/0.98  fd_pure                                 0
% 2.37/0.98  fd_pseudo                               0
% 2.37/0.98  fd_cond                                 0
% 2.37/0.98  fd_pseudo_cond                          0
% 2.37/0.98  AC symbols                              0
% 2.37/0.98  
% 2.37/0.98  ------ Schedule dynamic 5 is on 
% 2.37/0.98  
% 2.37/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.37/0.98  
% 2.37/0.98  
% 2.37/0.98  ------ 
% 2.37/0.98  Current options:
% 2.37/0.98  ------ 
% 2.37/0.98  
% 2.37/0.98  ------ Input Options
% 2.37/0.98  
% 2.37/0.98  --out_options                           all
% 2.37/0.98  --tptp_safe_out                         true
% 2.37/0.98  --problem_path                          ""
% 2.37/0.98  --include_path                          ""
% 2.37/0.98  --clausifier                            res/vclausify_rel
% 2.37/0.98  --clausifier_options                    --mode clausify
% 2.37/0.98  --stdin                                 false
% 2.37/0.98  --stats_out                             all
% 2.37/0.98  
% 2.37/0.98  ------ General Options
% 2.37/0.98  
% 2.37/0.98  --fof                                   false
% 2.37/0.98  --time_out_real                         305.
% 2.37/0.98  --time_out_virtual                      -1.
% 2.37/0.98  --symbol_type_check                     false
% 2.37/0.98  --clausify_out                          false
% 2.37/0.98  --sig_cnt_out                           false
% 2.37/0.98  --trig_cnt_out                          false
% 2.37/0.98  --trig_cnt_out_tolerance                1.
% 2.37/0.98  --trig_cnt_out_sk_spl                   false
% 2.37/0.98  --abstr_cl_out                          false
% 2.37/0.98  
% 2.37/0.98  ------ Global Options
% 2.37/0.98  
% 2.37/0.98  --schedule                              default
% 2.37/0.98  --add_important_lit                     false
% 2.37/0.98  --prop_solver_per_cl                    1000
% 2.37/0.98  --min_unsat_core                        false
% 2.37/0.98  --soft_assumptions                      false
% 2.37/0.98  --soft_lemma_size                       3
% 2.37/0.98  --prop_impl_unit_size                   0
% 2.37/0.98  --prop_impl_unit                        []
% 2.37/0.98  --share_sel_clauses                     true
% 2.37/0.98  --reset_solvers                         false
% 2.37/0.98  --bc_imp_inh                            [conj_cone]
% 2.37/0.98  --conj_cone_tolerance                   3.
% 2.37/0.98  --extra_neg_conj                        none
% 2.37/0.98  --large_theory_mode                     true
% 2.37/0.98  --prolific_symb_bound                   200
% 2.37/0.98  --lt_threshold                          2000
% 2.37/0.98  --clause_weak_htbl                      true
% 2.37/0.98  --gc_record_bc_elim                     false
% 2.37/0.98  
% 2.37/0.98  ------ Preprocessing Options
% 2.37/0.98  
% 2.37/0.98  --preprocessing_flag                    true
% 2.37/0.98  --time_out_prep_mult                    0.1
% 2.37/0.98  --splitting_mode                        input
% 2.37/0.98  --splitting_grd                         true
% 2.37/0.98  --splitting_cvd                         false
% 2.37/0.98  --splitting_cvd_svl                     false
% 2.37/0.98  --splitting_nvd                         32
% 2.37/0.98  --sub_typing                            true
% 2.37/0.98  --prep_gs_sim                           true
% 2.37/0.98  --prep_unflatten                        true
% 2.37/0.98  --prep_res_sim                          true
% 2.37/0.98  --prep_upred                            true
% 2.37/0.98  --prep_sem_filter                       exhaustive
% 2.37/0.98  --prep_sem_filter_out                   false
% 2.37/0.98  --pred_elim                             true
% 2.37/0.98  --res_sim_input                         true
% 2.37/0.98  --eq_ax_congr_red                       true
% 2.37/0.98  --pure_diseq_elim                       true
% 2.37/0.98  --brand_transform                       false
% 2.37/0.98  --non_eq_to_eq                          false
% 2.37/0.98  --prep_def_merge                        true
% 2.37/0.98  --prep_def_merge_prop_impl              false
% 2.37/0.98  --prep_def_merge_mbd                    true
% 2.37/0.98  --prep_def_merge_tr_red                 false
% 2.37/0.98  --prep_def_merge_tr_cl                  false
% 2.37/0.98  --smt_preprocessing                     true
% 2.37/0.98  --smt_ac_axioms                         fast
% 2.37/0.98  --preprocessed_out                      false
% 2.37/0.98  --preprocessed_stats                    false
% 2.37/0.98  
% 2.37/0.98  ------ Abstraction refinement Options
% 2.37/0.98  
% 2.37/0.98  --abstr_ref                             []
% 2.37/0.98  --abstr_ref_prep                        false
% 2.37/0.98  --abstr_ref_until_sat                   false
% 2.37/0.98  --abstr_ref_sig_restrict                funpre
% 2.37/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.37/0.98  --abstr_ref_under                       []
% 2.37/0.98  
% 2.37/0.98  ------ SAT Options
% 2.37/0.98  
% 2.37/0.98  --sat_mode                              false
% 2.37/0.98  --sat_fm_restart_options                ""
% 2.37/0.98  --sat_gr_def                            false
% 2.37/0.98  --sat_epr_types                         true
% 2.37/0.98  --sat_non_cyclic_types                  false
% 2.37/0.98  --sat_finite_models                     false
% 2.37/0.98  --sat_fm_lemmas                         false
% 2.37/0.98  --sat_fm_prep                           false
% 2.37/0.98  --sat_fm_uc_incr                        true
% 2.37/0.98  --sat_out_model                         small
% 2.37/0.98  --sat_out_clauses                       false
% 2.37/0.98  
% 2.37/0.98  ------ QBF Options
% 2.37/0.98  
% 2.37/0.98  --qbf_mode                              false
% 2.37/0.98  --qbf_elim_univ                         false
% 2.37/0.98  --qbf_dom_inst                          none
% 2.37/0.98  --qbf_dom_pre_inst                      false
% 2.37/0.98  --qbf_sk_in                             false
% 2.37/0.98  --qbf_pred_elim                         true
% 2.37/0.98  --qbf_split                             512
% 2.37/0.98  
% 2.37/0.98  ------ BMC1 Options
% 2.37/0.98  
% 2.37/0.98  --bmc1_incremental                      false
% 2.37/0.98  --bmc1_axioms                           reachable_all
% 2.37/0.98  --bmc1_min_bound                        0
% 2.37/0.98  --bmc1_max_bound                        -1
% 2.37/0.98  --bmc1_max_bound_default                -1
% 2.37/0.98  --bmc1_symbol_reachability              true
% 2.37/0.98  --bmc1_property_lemmas                  false
% 2.37/0.98  --bmc1_k_induction                      false
% 2.37/0.98  --bmc1_non_equiv_states                 false
% 2.37/0.98  --bmc1_deadlock                         false
% 2.37/0.98  --bmc1_ucm                              false
% 2.37/0.98  --bmc1_add_unsat_core                   none
% 2.37/0.98  --bmc1_unsat_core_children              false
% 2.37/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.37/0.98  --bmc1_out_stat                         full
% 2.37/0.98  --bmc1_ground_init                      false
% 2.37/0.98  --bmc1_pre_inst_next_state              false
% 2.37/0.98  --bmc1_pre_inst_state                   false
% 2.37/0.98  --bmc1_pre_inst_reach_state             false
% 2.37/0.98  --bmc1_out_unsat_core                   false
% 2.37/0.98  --bmc1_aig_witness_out                  false
% 2.37/0.98  --bmc1_verbose                          false
% 2.37/0.98  --bmc1_dump_clauses_tptp                false
% 2.37/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.37/0.98  --bmc1_dump_file                        -
% 2.37/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.37/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.37/0.98  --bmc1_ucm_extend_mode                  1
% 2.37/0.98  --bmc1_ucm_init_mode                    2
% 2.37/0.98  --bmc1_ucm_cone_mode                    none
% 2.37/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.37/0.98  --bmc1_ucm_relax_model                  4
% 2.37/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.37/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.37/0.98  --bmc1_ucm_layered_model                none
% 2.37/0.98  --bmc1_ucm_max_lemma_size               10
% 2.37/0.98  
% 2.37/0.98  ------ AIG Options
% 2.37/0.98  
% 2.37/0.98  --aig_mode                              false
% 2.37/0.98  
% 2.37/0.98  ------ Instantiation Options
% 2.37/0.98  
% 2.37/0.98  --instantiation_flag                    true
% 2.37/0.98  --inst_sos_flag                         false
% 2.37/0.98  --inst_sos_phase                        true
% 2.37/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.37/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.37/0.98  --inst_lit_sel_side                     none
% 2.37/0.98  --inst_solver_per_active                1400
% 2.37/0.98  --inst_solver_calls_frac                1.
% 2.37/0.98  --inst_passive_queue_type               priority_queues
% 2.37/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.37/0.98  --inst_passive_queues_freq              [25;2]
% 2.37/0.98  --inst_dismatching                      true
% 2.37/0.98  --inst_eager_unprocessed_to_passive     true
% 2.37/0.98  --inst_prop_sim_given                   true
% 2.37/0.98  --inst_prop_sim_new                     false
% 2.37/0.98  --inst_subs_new                         false
% 2.37/0.98  --inst_eq_res_simp                      false
% 2.37/0.98  --inst_subs_given                       false
% 2.37/0.98  --inst_orphan_elimination               true
% 2.37/0.98  --inst_learning_loop_flag               true
% 2.37/0.98  --inst_learning_start                   3000
% 2.37/0.98  --inst_learning_factor                  2
% 2.37/0.98  --inst_start_prop_sim_after_learn       3
% 2.37/0.98  --inst_sel_renew                        solver
% 2.37/0.98  --inst_lit_activity_flag                true
% 2.37/0.98  --inst_restr_to_given                   false
% 2.37/0.98  --inst_activity_threshold               500
% 2.37/0.98  --inst_out_proof                        true
% 2.37/0.98  
% 2.37/0.98  ------ Resolution Options
% 2.37/0.98  
% 2.37/0.98  --resolution_flag                       false
% 2.37/0.98  --res_lit_sel                           adaptive
% 2.37/0.98  --res_lit_sel_side                      none
% 2.37/0.98  --res_ordering                          kbo
% 2.37/0.98  --res_to_prop_solver                    active
% 2.37/0.98  --res_prop_simpl_new                    false
% 2.37/0.98  --res_prop_simpl_given                  true
% 2.37/0.98  --res_passive_queue_type                priority_queues
% 2.37/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.37/0.98  --res_passive_queues_freq               [15;5]
% 2.37/0.98  --res_forward_subs                      full
% 2.37/0.98  --res_backward_subs                     full
% 2.37/0.98  --res_forward_subs_resolution           true
% 2.37/0.98  --res_backward_subs_resolution          true
% 2.37/0.98  --res_orphan_elimination                true
% 2.37/0.98  --res_time_limit                        2.
% 2.37/0.98  --res_out_proof                         true
% 2.37/0.98  
% 2.37/0.98  ------ Superposition Options
% 2.37/0.98  
% 2.37/0.98  --superposition_flag                    true
% 2.37/0.98  --sup_passive_queue_type                priority_queues
% 2.37/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.37/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.37/0.98  --demod_completeness_check              fast
% 2.37/0.98  --demod_use_ground                      true
% 2.37/0.98  --sup_to_prop_solver                    passive
% 2.37/0.98  --sup_prop_simpl_new                    true
% 2.37/0.98  --sup_prop_simpl_given                  true
% 2.37/0.98  --sup_fun_splitting                     false
% 2.37/0.98  --sup_smt_interval                      50000
% 2.37/0.98  
% 2.37/0.98  ------ Superposition Simplification Setup
% 2.37/0.98  
% 2.37/0.98  --sup_indices_passive                   []
% 2.37/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.37/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/0.98  --sup_full_bw                           [BwDemod]
% 2.37/0.98  --sup_immed_triv                        [TrivRules]
% 2.37/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.37/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/0.98  --sup_immed_bw_main                     []
% 2.37/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.37/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/0.98  
% 2.37/0.98  ------ Combination Options
% 2.37/0.98  
% 2.37/0.98  --comb_res_mult                         3
% 2.37/0.98  --comb_sup_mult                         2
% 2.37/0.98  --comb_inst_mult                        10
% 2.37/0.98  
% 2.37/0.98  ------ Debug Options
% 2.37/0.98  
% 2.37/0.98  --dbg_backtrace                         false
% 2.37/0.98  --dbg_dump_prop_clauses                 false
% 2.37/0.98  --dbg_dump_prop_clauses_file            -
% 2.37/0.98  --dbg_out_stat                          false
% 2.37/0.98  
% 2.37/0.98  
% 2.37/0.98  
% 2.37/0.98  
% 2.37/0.98  ------ Proving...
% 2.37/0.98  
% 2.37/0.98  
% 2.37/0.98  % SZS status Theorem for theBenchmark.p
% 2.37/0.98  
% 2.37/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.37/0.98  
% 2.37/0.98  fof(f4,conjecture,(
% 2.37/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 2.37/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/0.98  
% 2.37/0.98  fof(f5,negated_conjecture,(
% 2.37/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 2.37/0.98    inference(negated_conjecture,[],[f4])).
% 2.37/0.98  
% 2.37/0.98  fof(f12,plain,(
% 2.37/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.37/0.98    inference(ennf_transformation,[],[f5])).
% 2.37/0.98  
% 2.37/0.98  fof(f13,plain,(
% 2.37/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.37/0.98    inference(flattening,[],[f12])).
% 2.37/0.98  
% 2.37/0.98  fof(f24,plain,(
% 2.37/0.98    ( ! [X2,X0,X1] : (? [X3] : ((k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((k2_tsep_1(X0,X2,k1_tsep_1(X0,sK5,X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,sK5)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (r1_tsep_1(sK5,X2) | r1_tsep_1(X2,sK5)) & m1_pre_topc(X1,X2) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 2.37/0.98    introduced(choice_axiom,[])).
% 2.37/0.98  
% 2.37/0.98  fof(f23,plain,(
% 2.37/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : ((k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : ((k2_tsep_1(X0,sK4,k1_tsep_1(X0,X3,X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | k2_tsep_1(X0,sK4,k1_tsep_1(X0,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (r1_tsep_1(X3,sK4) | r1_tsep_1(sK4,X3)) & m1_pre_topc(X1,sK4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.37/0.98    introduced(choice_axiom,[])).
% 2.37/0.98  
% 2.37/0.98  fof(f22,plain,(
% 2.37/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,sK3)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | k2_tsep_1(X0,X2,k1_tsep_1(X0,sK3,X3)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(sK3,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.37/0.98    introduced(choice_axiom,[])).
% 2.37/0.98  
% 2.37/0.98  fof(f21,plain,(
% 2.37/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((k2_tsep_1(sK2,X2,k1_tsep_1(sK2,X3,X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | k2_tsep_1(sK2,X2,k1_tsep_1(sK2,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.37/0.98    introduced(choice_axiom,[])).
% 2.37/0.98  
% 2.37/0.98  fof(f25,plain,(
% 2.37/0.98    ((((k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) & (r1_tsep_1(sK5,sK4) | r1_tsep_1(sK4,sK5)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.37/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f13,f24,f23,f22,f21])).
% 2.37/0.98  
% 2.37/0.98  fof(f54,plain,(
% 2.37/0.98    m1_pre_topc(sK3,sK2)),
% 2.37/0.98    inference(cnf_transformation,[],[f25])).
% 2.37/0.98  
% 2.37/0.98  fof(f56,plain,(
% 2.37/0.98    m1_pre_topc(sK4,sK2)),
% 2.37/0.98    inference(cnf_transformation,[],[f25])).
% 2.37/0.98  
% 2.37/0.98  fof(f58,plain,(
% 2.37/0.98    m1_pre_topc(sK5,sK2)),
% 2.37/0.98    inference(cnf_transformation,[],[f25])).
% 2.37/0.98  
% 2.37/0.98  fof(f60,plain,(
% 2.37/0.98    r1_tsep_1(sK5,sK4) | r1_tsep_1(sK4,sK5)),
% 2.37/0.98    inference(cnf_transformation,[],[f25])).
% 2.37/0.98  
% 2.37/0.98  fof(f15,plain,(
% 2.37/0.98    ! [X3,X1,X0,X2] : ((k2_tsep_1(X0,X2,X1) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) & k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2)) | (~r1_tsep_1(X2,X3) & ~r1_tsep_1(X3,X2)) | (r1_tsep_1(X2,X1) & r1_tsep_1(X1,X2)) | ~sP1(X3,X1,X0,X2))),
% 2.37/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.37/0.98  
% 2.37/0.98  fof(f17,plain,(
% 2.37/0.98    ! [X3,X1,X0,X2] : ((k2_tsep_1(X0,X2,X1) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) & k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2)) | (~r1_tsep_1(X2,X3) & ~r1_tsep_1(X3,X2)) | (r1_tsep_1(X2,X1) & r1_tsep_1(X1,X2)) | ~sP1(X3,X1,X0,X2))),
% 2.37/0.98    inference(nnf_transformation,[],[f15])).
% 2.37/0.98  
% 2.37/0.98  fof(f18,plain,(
% 2.37/0.98    ! [X0,X1,X2,X3] : ((k2_tsep_1(X2,X3,X1) = k2_tsep_1(X2,X3,k1_tsep_1(X2,X1,X0)) & k2_tsep_1(X2,X1,X3) = k2_tsep_1(X2,k1_tsep_1(X2,X1,X0),X3)) | (~r1_tsep_1(X3,X0) & ~r1_tsep_1(X0,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | ~sP1(X0,X1,X2,X3))),
% 2.37/0.98    inference(rectify,[],[f17])).
% 2.37/0.98  
% 2.37/0.98  fof(f30,plain,(
% 2.37/0.98    ( ! [X2,X0,X3,X1] : (k2_tsep_1(X2,X1,X3) = k2_tsep_1(X2,k1_tsep_1(X2,X1,X0),X3) | ~r1_tsep_1(X3,X0) | r1_tsep_1(X1,X3) | ~sP1(X0,X1,X2,X3)) )),
% 2.37/0.98    inference(cnf_transformation,[],[f18])).
% 2.37/0.98  
% 2.37/0.98  fof(f2,axiom,(
% 2.37/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~(~(k2_tsep_1(X0,X2,X1) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) & k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2)) & (r1_tsep_1(X2,X3) | r1_tsep_1(X3,X2)) & ~(r1_tsep_1(X2,X1) & r1_tsep_1(X1,X2))) & ~(~(k2_tsep_1(X0,X2,X3) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) & k2_tsep_1(X0,X3,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2)) & ~(r1_tsep_1(X2,X3) & r1_tsep_1(X3,X2)) & (r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2))))))))),
% 2.37/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/0.98  
% 2.37/0.98  fof(f8,plain,(
% 2.37/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((k2_tsep_1(X0,X2,X1) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) & k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2)) | (~r1_tsep_1(X2,X3) & ~r1_tsep_1(X3,X2)) | (r1_tsep_1(X2,X1) & r1_tsep_1(X1,X2))) & ((k2_tsep_1(X0,X2,X3) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) & k2_tsep_1(X0,X3,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2)) | (r1_tsep_1(X2,X3) & r1_tsep_1(X3,X2)) | (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.37/0.98    inference(ennf_transformation,[],[f2])).
% 2.37/0.98  
% 2.37/0.98  fof(f9,plain,(
% 2.37/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((k2_tsep_1(X0,X2,X1) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) & k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2)) | (~r1_tsep_1(X2,X3) & ~r1_tsep_1(X3,X2)) | (r1_tsep_1(X2,X1) & r1_tsep_1(X1,X2))) & ((k2_tsep_1(X0,X2,X3) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) & k2_tsep_1(X0,X3,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2)) | (r1_tsep_1(X2,X3) & r1_tsep_1(X3,X2)) | (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.37/0.98    inference(flattening,[],[f8])).
% 2.37/0.98  
% 2.37/0.98  fof(f14,plain,(
% 2.37/0.98    ! [X3,X1,X0,X2] : ((k2_tsep_1(X0,X2,X3) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) & k2_tsep_1(X0,X3,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2)) | (r1_tsep_1(X2,X3) & r1_tsep_1(X3,X2)) | (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~sP0(X3,X1,X0,X2))),
% 2.37/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.37/0.98  
% 2.37/0.98  fof(f16,plain,(
% 2.37/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((sP1(X3,X1,X0,X2) & sP0(X3,X1,X0,X2)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.37/0.98    inference(definition_folding,[],[f9,f15,f14])).
% 2.37/0.98  
% 2.37/0.98  fof(f45,plain,(
% 2.37/0.98    ( ! [X2,X0,X3,X1] : (sP1(X3,X1,X0,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.37/0.98    inference(cnf_transformation,[],[f16])).
% 2.37/0.98  
% 2.37/0.98  fof(f52,plain,(
% 2.37/0.98    l1_pre_topc(sK2)),
% 2.37/0.98    inference(cnf_transformation,[],[f25])).
% 2.37/0.98  
% 2.37/0.98  fof(f50,plain,(
% 2.37/0.98    ~v2_struct_0(sK2)),
% 2.37/0.98    inference(cnf_transformation,[],[f25])).
% 2.37/0.98  
% 2.37/0.98  fof(f51,plain,(
% 2.37/0.98    v2_pre_topc(sK2)),
% 2.37/0.98    inference(cnf_transformation,[],[f25])).
% 2.37/0.98  
% 2.37/0.98  fof(f53,plain,(
% 2.37/0.98    ~v2_struct_0(sK3)),
% 2.37/0.98    inference(cnf_transformation,[],[f25])).
% 2.37/0.98  
% 2.37/0.98  fof(f55,plain,(
% 2.37/0.98    ~v2_struct_0(sK4)),
% 2.37/0.98    inference(cnf_transformation,[],[f25])).
% 2.37/0.98  
% 2.37/0.98  fof(f57,plain,(
% 2.37/0.98    ~v2_struct_0(sK5)),
% 2.37/0.98    inference(cnf_transformation,[],[f25])).
% 2.37/0.98  
% 2.37/0.98  fof(f59,plain,(
% 2.37/0.98    m1_pre_topc(sK3,sK4)),
% 2.37/0.98    inference(cnf_transformation,[],[f25])).
% 2.37/0.98  
% 2.37/0.98  fof(f1,axiom,(
% 2.37/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 2.37/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/0.98  
% 2.37/0.98  fof(f6,plain,(
% 2.37/0.98    ! [X0] : (! [X1] : (! [X2] : (((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.37/0.98    inference(ennf_transformation,[],[f1])).
% 2.37/0.98  
% 2.37/0.98  fof(f7,plain,(
% 2.37/0.98    ! [X0] : (! [X1] : (! [X2] : ((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.37/0.98    inference(flattening,[],[f6])).
% 2.37/0.98  
% 2.37/0.98  fof(f27,plain,(
% 2.37/0.98    ( ! [X2,X0,X1] : (~r1_tsep_1(X2,X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.37/0.98    inference(cnf_transformation,[],[f7])).
% 2.37/0.98  
% 2.37/0.98  fof(f3,axiom,(
% 2.37/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ((k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => m1_pre_topc(X2,X1)) & (m1_pre_topc(X2,X1) => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) => m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))))),
% 2.37/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/0.98  
% 2.37/0.98  fof(f10,plain,(
% 2.37/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X2,X1) | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X2,X1)) & (m1_pre_topc(X1,X2) | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X2))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.37/0.98    inference(ennf_transformation,[],[f3])).
% 2.37/0.98  
% 2.37/0.98  fof(f11,plain,(
% 2.37/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X2,X1) | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X2,X1)) & (m1_pre_topc(X1,X2) | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X2))) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.37/0.98    inference(flattening,[],[f10])).
% 2.37/0.98  
% 2.37/0.98  fof(f48,plain,(
% 2.37/0.98    ( ! [X2,X0,X1] : (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X2,X1) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.37/0.98    inference(cnf_transformation,[],[f11])).
% 2.37/0.98  
% 2.37/0.98  fof(f46,plain,(
% 2.37/0.98    ( ! [X2,X0,X1] : (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X2) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.37/0.98    inference(cnf_transformation,[],[f11])).
% 2.37/0.98  
% 2.37/0.98  fof(f26,plain,(
% 2.37/0.98    ( ! [X2,X0,X1] : (~r1_tsep_1(X1,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.37/0.98    inference(cnf_transformation,[],[f7])).
% 2.37/0.98  
% 2.37/0.98  fof(f61,plain,(
% 2.37/0.98    k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 2.37/0.98    inference(cnf_transformation,[],[f25])).
% 2.37/0.98  
% 2.37/0.98  fof(f19,plain,(
% 2.37/0.98    ! [X3,X1,X0,X2] : ((k2_tsep_1(X0,X2,X3) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) & k2_tsep_1(X0,X3,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2)) | (r1_tsep_1(X2,X3) & r1_tsep_1(X3,X2)) | (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~sP0(X3,X1,X0,X2))),
% 2.37/0.98    inference(nnf_transformation,[],[f14])).
% 2.37/0.98  
% 2.37/0.98  fof(f20,plain,(
% 2.37/0.98    ! [X0,X1,X2,X3] : ((k2_tsep_1(X2,X3,X0) = k2_tsep_1(X2,X3,k1_tsep_1(X2,X1,X0)) & k2_tsep_1(X2,X0,X3) = k2_tsep_1(X2,k1_tsep_1(X2,X1,X0),X3)) | (r1_tsep_1(X3,X0) & r1_tsep_1(X0,X3)) | (~r1_tsep_1(X3,X1) & ~r1_tsep_1(X1,X3)) | ~sP0(X0,X1,X2,X3))),
% 2.37/0.98    inference(rectify,[],[f19])).
% 2.37/0.98  
% 2.37/0.98  fof(f43,plain,(
% 2.37/0.98    ( ! [X2,X0,X3,X1] : (k2_tsep_1(X2,X3,X0) = k2_tsep_1(X2,X3,k1_tsep_1(X2,X1,X0)) | r1_tsep_1(X3,X0) | ~r1_tsep_1(X3,X1) | ~sP0(X0,X1,X2,X3)) )),
% 2.37/0.98    inference(cnf_transformation,[],[f20])).
% 2.37/0.98  
% 2.37/0.98  fof(f44,plain,(
% 2.37/0.98    ( ! [X2,X0,X3,X1] : (sP0(X3,X1,X0,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.37/0.98    inference(cnf_transformation,[],[f16])).
% 2.37/0.98  
% 2.37/0.98  fof(f42,plain,(
% 2.37/0.98    ( ! [X2,X0,X3,X1] : (k2_tsep_1(X2,X3,X0) = k2_tsep_1(X2,X3,k1_tsep_1(X2,X1,X0)) | r1_tsep_1(X3,X0) | ~r1_tsep_1(X1,X3) | ~sP0(X0,X1,X2,X3)) )),
% 2.37/0.98    inference(cnf_transformation,[],[f20])).
% 2.37/0.98  
% 2.37/0.98  fof(f35,plain,(
% 2.37/0.98    ( ! [X2,X0,X3,X1] : (k2_tsep_1(X2,X3,X1) = k2_tsep_1(X2,X3,k1_tsep_1(X2,X1,X0)) | ~r1_tsep_1(X3,X0) | r1_tsep_1(X3,X1) | ~sP1(X0,X1,X2,X3)) )),
% 2.37/0.98    inference(cnf_transformation,[],[f18])).
% 2.37/0.98  
% 2.37/0.98  fof(f29,plain,(
% 2.37/0.98    ( ! [X2,X0,X3,X1] : (k2_tsep_1(X2,X1,X3) = k2_tsep_1(X2,k1_tsep_1(X2,X1,X0),X3) | ~r1_tsep_1(X0,X3) | r1_tsep_1(X3,X1) | ~sP1(X0,X1,X2,X3)) )),
% 2.37/0.98    inference(cnf_transformation,[],[f18])).
% 2.37/0.98  
% 2.37/0.98  fof(f32,plain,(
% 2.37/0.98    ( ! [X2,X0,X3,X1] : (k2_tsep_1(X2,X3,X1) = k2_tsep_1(X2,X3,k1_tsep_1(X2,X1,X0)) | ~r1_tsep_1(X0,X3) | r1_tsep_1(X1,X3) | ~sP1(X0,X1,X2,X3)) )),
% 2.37/0.98    inference(cnf_transformation,[],[f18])).
% 2.37/0.98  
% 2.37/0.98  cnf(c_31,negated_conjecture,
% 2.37/0.98      ( m1_pre_topc(sK3,sK2) ),
% 2.37/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_1519,negated_conjecture,
% 2.37/0.98      ( m1_pre_topc(sK3,sK2) ),
% 2.37/0.98      inference(subtyping,[status(esa)],[c_31]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_1818,plain,
% 2.37/0.98      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 2.37/0.98      inference(predicate_to_equality,[status(thm)],[c_1519]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_29,negated_conjecture,
% 2.37/0.98      ( m1_pre_topc(sK4,sK2) ),
% 2.37/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_1521,negated_conjecture,
% 2.37/0.98      ( m1_pre_topc(sK4,sK2) ),
% 2.37/0.98      inference(subtyping,[status(esa)],[c_29]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_1816,plain,
% 2.37/0.98      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 2.37/0.98      inference(predicate_to_equality,[status(thm)],[c_1521]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_27,negated_conjecture,
% 2.37/0.98      ( m1_pre_topc(sK5,sK2) ),
% 2.37/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_1523,negated_conjecture,
% 2.37/0.98      ( m1_pre_topc(sK5,sK2) ),
% 2.37/0.98      inference(subtyping,[status(esa)],[c_27]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_1814,plain,
% 2.37/0.98      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 2.37/0.98      inference(predicate_to_equality,[status(thm)],[c_1523]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_25,negated_conjecture,
% 2.37/0.98      ( r1_tsep_1(sK5,sK4) | r1_tsep_1(sK4,sK5) ),
% 2.37/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_1525,negated_conjecture,
% 2.37/0.98      ( r1_tsep_1(sK5,sK4) | r1_tsep_1(sK4,sK5) ),
% 2.37/0.98      inference(subtyping,[status(esa)],[c_25]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_1812,plain,
% 2.37/0.98      ( r1_tsep_1(sK5,sK4) = iProver_top
% 2.37/0.98      | r1_tsep_1(sK4,sK5) = iProver_top ),
% 2.37/0.98      inference(predicate_to_equality,[status(thm)],[c_1525]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_7,plain,
% 2.37/0.98      ( ~ sP1(X0,X1,X2,X3)
% 2.37/0.98      | ~ r1_tsep_1(X3,X0)
% 2.37/0.98      | r1_tsep_1(X1,X3)
% 2.37/0.98      | k2_tsep_1(X2,k1_tsep_1(X2,X1,X0),X3) = k2_tsep_1(X2,X1,X3) ),
% 2.37/0.98      inference(cnf_transformation,[],[f30]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_18,plain,
% 2.37/0.98      ( sP1(X0,X1,X2,X3)
% 2.37/0.98      | ~ m1_pre_topc(X3,X2)
% 2.37/0.98      | ~ m1_pre_topc(X1,X2)
% 2.37/0.98      | ~ m1_pre_topc(X0,X2)
% 2.37/0.98      | ~ v2_pre_topc(X2)
% 2.37/0.98      | ~ l1_pre_topc(X2)
% 2.37/0.98      | v2_struct_0(X2)
% 2.37/0.98      | v2_struct_0(X1)
% 2.37/0.98      | v2_struct_0(X3)
% 2.37/0.98      | v2_struct_0(X0) ),
% 2.37/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_33,negated_conjecture,
% 2.37/0.98      ( l1_pre_topc(sK2) ),
% 2.37/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_377,plain,
% 2.37/0.98      ( sP1(X0,X1,X2,X3)
% 2.37/0.98      | ~ m1_pre_topc(X0,X2)
% 2.37/0.98      | ~ m1_pre_topc(X1,X2)
% 2.37/0.98      | ~ m1_pre_topc(X3,X2)
% 2.37/0.98      | ~ v2_pre_topc(X2)
% 2.37/0.98      | v2_struct_0(X2)
% 2.37/0.98      | v2_struct_0(X1)
% 2.37/0.98      | v2_struct_0(X0)
% 2.37/0.98      | v2_struct_0(X3)
% 2.37/0.98      | sK2 != X2 ),
% 2.37/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_33]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_378,plain,
% 2.37/0.98      ( sP1(X0,X1,sK2,X2)
% 2.37/0.98      | ~ m1_pre_topc(X2,sK2)
% 2.37/0.98      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.98      | ~ m1_pre_topc(X0,sK2)
% 2.37/0.98      | ~ v2_pre_topc(sK2)
% 2.37/0.98      | v2_struct_0(X1)
% 2.37/0.98      | v2_struct_0(X0)
% 2.37/0.98      | v2_struct_0(X2)
% 2.37/0.98      | v2_struct_0(sK2) ),
% 2.37/0.98      inference(unflattening,[status(thm)],[c_377]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_35,negated_conjecture,
% 2.37/0.98      ( ~ v2_struct_0(sK2) ),
% 2.37/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_34,negated_conjecture,
% 2.37/0.98      ( v2_pre_topc(sK2) ),
% 2.37/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_382,plain,
% 2.37/0.98      ( v2_struct_0(X2)
% 2.37/0.98      | v2_struct_0(X0)
% 2.37/0.98      | v2_struct_0(X1)
% 2.37/0.98      | sP1(X0,X1,sK2,X2)
% 2.37/0.98      | ~ m1_pre_topc(X2,sK2)
% 2.37/0.98      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.98      | ~ m1_pre_topc(X0,sK2) ),
% 2.37/0.98      inference(global_propositional_subsumption,
% 2.37/0.98                [status(thm)],
% 2.37/0.98                [c_378,c_35,c_34]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_383,plain,
% 2.37/0.98      ( sP1(X0,X1,sK2,X2)
% 2.37/0.98      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.98      | ~ m1_pre_topc(X0,sK2)
% 2.37/0.98      | ~ m1_pre_topc(X2,sK2)
% 2.37/0.98      | v2_struct_0(X2)
% 2.37/0.98      | v2_struct_0(X1)
% 2.37/0.98      | v2_struct_0(X0) ),
% 2.37/0.98      inference(renaming,[status(thm)],[c_382]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_703,plain,
% 2.37/0.98      ( ~ m1_pre_topc(X0,sK2)
% 2.37/0.98      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.98      | ~ m1_pre_topc(X2,sK2)
% 2.37/0.98      | ~ r1_tsep_1(X3,X4)
% 2.37/0.98      | r1_tsep_1(X5,X3)
% 2.37/0.98      | v2_struct_0(X2)
% 2.37/0.98      | v2_struct_0(X0)
% 2.37/0.98      | v2_struct_0(X1)
% 2.37/0.98      | X2 != X3
% 2.37/0.98      | X0 != X5
% 2.37/0.98      | X1 != X4
% 2.37/0.98      | k2_tsep_1(X6,k1_tsep_1(X6,X5,X4),X3) = k2_tsep_1(X6,X5,X3)
% 2.37/0.98      | sK2 != X6 ),
% 2.37/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_383]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_704,plain,
% 2.37/0.98      ( ~ m1_pre_topc(X0,sK2)
% 2.37/0.98      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.98      | ~ m1_pre_topc(X2,sK2)
% 2.37/0.98      | ~ r1_tsep_1(X0,X2)
% 2.37/0.98      | r1_tsep_1(X1,X0)
% 2.37/0.98      | v2_struct_0(X0)
% 2.37/0.98      | v2_struct_0(X1)
% 2.37/0.98      | v2_struct_0(X2)
% 2.37/0.98      | k2_tsep_1(sK2,k1_tsep_1(sK2,X1,X2),X0) = k2_tsep_1(sK2,X1,X0) ),
% 2.37/0.98      inference(unflattening,[status(thm)],[c_703]) ).
% 2.37/0.98  
% 2.37/0.98  cnf(c_1508,plain,
% 2.37/0.98      ( ~ m1_pre_topc(X0_44,sK2)
% 2.37/0.98      | ~ m1_pre_topc(X1_44,sK2)
% 2.37/0.98      | ~ m1_pre_topc(X2_44,sK2)
% 2.37/0.98      | ~ r1_tsep_1(X0_44,X2_44)
% 2.37/0.99      | r1_tsep_1(X1_44,X0_44)
% 2.37/0.99      | v2_struct_0(X0_44)
% 2.37/0.99      | v2_struct_0(X1_44)
% 2.37/0.99      | v2_struct_0(X2_44)
% 2.37/0.99      | k2_tsep_1(sK2,k1_tsep_1(sK2,X1_44,X2_44),X0_44) = k2_tsep_1(sK2,X1_44,X0_44) ),
% 2.37/0.99      inference(subtyping,[status(esa)],[c_704]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1829,plain,
% 2.37/0.99      ( k2_tsep_1(sK2,k1_tsep_1(sK2,X0_44,X1_44),X2_44) = k2_tsep_1(sK2,X0_44,X2_44)
% 2.37/0.99      | m1_pre_topc(X1_44,sK2) != iProver_top
% 2.37/0.99      | m1_pre_topc(X0_44,sK2) != iProver_top
% 2.37/0.99      | m1_pre_topc(X2_44,sK2) != iProver_top
% 2.37/0.99      | r1_tsep_1(X2_44,X1_44) != iProver_top
% 2.37/0.99      | r1_tsep_1(X0_44,X2_44) = iProver_top
% 2.37/0.99      | v2_struct_0(X0_44) = iProver_top
% 2.37/0.99      | v2_struct_0(X2_44) = iProver_top
% 2.37/0.99      | v2_struct_0(X1_44) = iProver_top ),
% 2.37/0.99      inference(predicate_to_equality,[status(thm)],[c_1508]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_4463,plain,
% 2.37/0.99      ( k2_tsep_1(sK2,k1_tsep_1(sK2,X0_44,sK4),sK5) = k2_tsep_1(sK2,X0_44,sK5)
% 2.37/0.99      | m1_pre_topc(X0_44,sK2) != iProver_top
% 2.37/0.99      | m1_pre_topc(sK5,sK2) != iProver_top
% 2.37/0.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 2.37/0.99      | r1_tsep_1(X0_44,sK5) = iProver_top
% 2.37/0.99      | r1_tsep_1(sK4,sK5) = iProver_top
% 2.37/0.99      | v2_struct_0(X0_44) = iProver_top
% 2.37/0.99      | v2_struct_0(sK5) = iProver_top
% 2.37/0.99      | v2_struct_0(sK4) = iProver_top ),
% 2.37/0.99      inference(superposition,[status(thm)],[c_1812,c_1829]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_32,negated_conjecture,
% 2.37/0.99      ( ~ v2_struct_0(sK3) ),
% 2.37/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_39,plain,
% 2.37/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 2.37/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_40,plain,
% 2.37/0.99      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 2.37/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_30,negated_conjecture,
% 2.37/0.99      ( ~ v2_struct_0(sK4) ),
% 2.37/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_41,plain,
% 2.37/0.99      ( v2_struct_0(sK4) != iProver_top ),
% 2.37/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_42,plain,
% 2.37/0.99      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 2.37/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_28,negated_conjecture,
% 2.37/0.99      ( ~ v2_struct_0(sK5) ),
% 2.37/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_43,plain,
% 2.37/0.99      ( v2_struct_0(sK5) != iProver_top ),
% 2.37/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_44,plain,
% 2.37/0.99      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 2.37/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_26,negated_conjecture,
% 2.37/0.99      ( m1_pre_topc(sK3,sK4) ),
% 2.37/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_45,plain,
% 2.37/0.99      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 2.37/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_0,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | ~ m1_pre_topc(X1,X2)
% 2.37/0.99      | ~ m1_pre_topc(X0,X2)
% 2.37/0.99      | ~ r1_tsep_1(X1,X0)
% 2.37/0.99      | ~ v2_pre_topc(X2)
% 2.37/0.99      | ~ l1_pre_topc(X2)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(X1) ),
% 2.37/0.99      inference(cnf_transformation,[],[f27]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_440,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | ~ m1_pre_topc(X2,X1)
% 2.37/0.99      | ~ m1_pre_topc(X0,X2)
% 2.37/0.99      | ~ r1_tsep_1(X2,X0)
% 2.37/0.99      | ~ v2_pre_topc(X1)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | sK2 != X1 ),
% 2.37/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_33]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_441,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X1,X0)
% 2.37/0.99      | ~ v2_pre_topc(sK2)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(sK2) ),
% 2.37/0.99      inference(unflattening,[status(thm)],[c_440]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_443,plain,
% 2.37/0.99      ( v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X1,X0) ),
% 2.37/0.99      inference(global_propositional_subsumption,
% 2.37/0.99                [status(thm)],
% 2.37/0.99                [c_441,c_35,c_34]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_444,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X1,X0)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X0) ),
% 2.37/0.99      inference(renaming,[status(thm)],[c_443]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1515,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0_44,X1_44)
% 2.37/0.99      | ~ m1_pre_topc(X0_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1_44,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X1_44,X0_44)
% 2.37/0.99      | v2_struct_0(X0_44)
% 2.37/0.99      | v2_struct_0(X1_44) ),
% 2.37/0.99      inference(subtyping,[status(esa)],[c_444]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_2307,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(sK3,X0_44)
% 2.37/0.99      | ~ m1_pre_topc(sK3,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X0_44,sK3)
% 2.37/0.99      | v2_struct_0(X0_44)
% 2.37/0.99      | v2_struct_0(sK3) ),
% 2.37/0.99      inference(instantiation,[status(thm)],[c_1515]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_2508,plain,
% 2.37/0.99      ( ~ m1_pre_topc(sK3,sK4)
% 2.37/0.99      | ~ m1_pre_topc(sK3,sK2)
% 2.37/0.99      | ~ m1_pre_topc(sK4,sK2)
% 2.37/0.99      | ~ r1_tsep_1(sK4,sK3)
% 2.37/0.99      | v2_struct_0(sK3)
% 2.37/0.99      | v2_struct_0(sK4) ),
% 2.37/0.99      inference(instantiation,[status(thm)],[c_2307]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_2509,plain,
% 2.37/0.99      ( m1_pre_topc(sK3,sK4) != iProver_top
% 2.37/0.99      | m1_pre_topc(sK3,sK2) != iProver_top
% 2.37/0.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 2.37/0.99      | r1_tsep_1(sK4,sK3) != iProver_top
% 2.37/0.99      | v2_struct_0(sK3) = iProver_top
% 2.37/0.99      | v2_struct_0(sK4) = iProver_top ),
% 2.37/0.99      inference(predicate_to_equality,[status(thm)],[c_2508]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1524,negated_conjecture,
% 2.37/0.99      ( m1_pre_topc(sK3,sK4) ),
% 2.37/0.99      inference(subtyping,[status(esa)],[c_26]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1813,plain,
% 2.37/0.99      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 2.37/0.99      inference(predicate_to_equality,[status(thm)],[c_1524]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_21,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | ~ m1_pre_topc(X2,X1)
% 2.37/0.99      | ~ m1_pre_topc(X0,X2)
% 2.37/0.99      | r1_tsep_1(X2,X0)
% 2.37/0.99      | ~ v2_pre_topc(X1)
% 2.37/0.99      | ~ l1_pre_topc(X1)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(X1,X2,X0) ),
% 2.37/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_525,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | ~ m1_pre_topc(X0,X2)
% 2.37/0.99      | ~ m1_pre_topc(X1,X2)
% 2.37/0.99      | r1_tsep_1(X1,X0)
% 2.37/0.99      | ~ v2_pre_topc(X2)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(X2,X1,X0)
% 2.37/0.99      | sK2 != X2 ),
% 2.37/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_33]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_526,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | r1_tsep_1(X1,X0)
% 2.37/0.99      | ~ v2_pre_topc(sK2)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(sK2)
% 2.37/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK2,X1,X0) ),
% 2.37/0.99      inference(unflattening,[status(thm)],[c_525]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_529,plain,
% 2.37/0.99      ( v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK2,X1,X0) ),
% 2.37/0.99      inference(global_propositional_subsumption,
% 2.37/0.99                [status(thm)],
% 2.37/0.99                [c_526,c_35,c_34,c_444]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_530,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK2,X1,X0) ),
% 2.37/0.99      inference(renaming,[status(thm)],[c_529]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1512,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0_44,X1_44)
% 2.37/0.99      | ~ m1_pre_topc(X0_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1_44,sK2)
% 2.37/0.99      | v2_struct_0(X0_44)
% 2.37/0.99      | v2_struct_0(X1_44)
% 2.37/0.99      | g1_pre_topc(u1_struct_0(X0_44),u1_pre_topc(X0_44)) = k2_tsep_1(sK2,X1_44,X0_44) ),
% 2.37/0.99      inference(subtyping,[status(esa)],[c_530]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1825,plain,
% 2.37/0.99      ( g1_pre_topc(u1_struct_0(X0_44),u1_pre_topc(X0_44)) = k2_tsep_1(sK2,X1_44,X0_44)
% 2.37/0.99      | m1_pre_topc(X0_44,X1_44) != iProver_top
% 2.37/0.99      | m1_pre_topc(X1_44,sK2) != iProver_top
% 2.37/0.99      | m1_pre_topc(X0_44,sK2) != iProver_top
% 2.37/0.99      | v2_struct_0(X1_44) = iProver_top
% 2.37/0.99      | v2_struct_0(X0_44) = iProver_top ),
% 2.37/0.99      inference(predicate_to_equality,[status(thm)],[c_1512]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_3892,plain,
% 2.37/0.99      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK4,sK3)
% 2.37/0.99      | m1_pre_topc(sK3,sK2) != iProver_top
% 2.37/0.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 2.37/0.99      | v2_struct_0(sK3) = iProver_top
% 2.37/0.99      | v2_struct_0(sK4) = iProver_top ),
% 2.37/0.99      inference(superposition,[status(thm)],[c_1813,c_1825]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_23,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | ~ m1_pre_topc(X1,X2)
% 2.37/0.99      | ~ m1_pre_topc(X0,X2)
% 2.37/0.99      | r1_tsep_1(X0,X1)
% 2.37/0.99      | ~ v2_pre_topc(X2)
% 2.37/0.99      | ~ l1_pre_topc(X2)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(X2,X0,X1) ),
% 2.37/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | ~ m1_pre_topc(X1,X2)
% 2.37/0.99      | ~ m1_pre_topc(X0,X2)
% 2.37/0.99      | ~ r1_tsep_1(X0,X1)
% 2.37/0.99      | ~ v2_pre_topc(X2)
% 2.37/0.99      | ~ l1_pre_topc(X2)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(X1) ),
% 2.37/0.99      inference(cnf_transformation,[],[f26]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_161,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,X2)
% 2.37/0.99      | ~ m1_pre_topc(X1,X2)
% 2.37/0.99      | ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | ~ v2_pre_topc(X2)
% 2.37/0.99      | ~ l1_pre_topc(X2)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(X2,X0,X1) ),
% 2.37/0.99      inference(global_propositional_subsumption,
% 2.37/0.99                [status(thm)],
% 2.37/0.99                [c_23,c_1]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_162,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | ~ m1_pre_topc(X2,X1)
% 2.37/0.99      | ~ m1_pre_topc(X0,X2)
% 2.37/0.99      | ~ v2_pre_topc(X1)
% 2.37/0.99      | ~ l1_pre_topc(X1)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(X1,X0,X2) ),
% 2.37/0.99      inference(renaming,[status(thm)],[c_161]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_466,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | ~ m1_pre_topc(X0,X2)
% 2.37/0.99      | ~ m1_pre_topc(X1,X2)
% 2.37/0.99      | ~ v2_pre_topc(X2)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(X2,X0,X1)
% 2.37/0.99      | sK2 != X2 ),
% 2.37/0.99      inference(resolution_lifted,[status(thm)],[c_162,c_33]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_467,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | ~ v2_pre_topc(sK2)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(sK2)
% 2.37/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK2,X0,X1) ),
% 2.37/0.99      inference(unflattening,[status(thm)],[c_466]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_471,plain,
% 2.37/0.99      ( v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK2,X0,X1) ),
% 2.37/0.99      inference(global_propositional_subsumption,
% 2.37/0.99                [status(thm)],
% 2.37/0.99                [c_467,c_35,c_34]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_472,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK2,X0,X1) ),
% 2.37/0.99      inference(renaming,[status(thm)],[c_471]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1514,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0_44,X1_44)
% 2.37/0.99      | ~ m1_pre_topc(X0_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1_44,sK2)
% 2.37/0.99      | v2_struct_0(X0_44)
% 2.37/0.99      | v2_struct_0(X1_44)
% 2.37/0.99      | g1_pre_topc(u1_struct_0(X0_44),u1_pre_topc(X0_44)) = k2_tsep_1(sK2,X0_44,X1_44) ),
% 2.37/0.99      inference(subtyping,[status(esa)],[c_472]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1823,plain,
% 2.37/0.99      ( g1_pre_topc(u1_struct_0(X0_44),u1_pre_topc(X0_44)) = k2_tsep_1(sK2,X0_44,X1_44)
% 2.37/0.99      | m1_pre_topc(X0_44,X1_44) != iProver_top
% 2.37/0.99      | m1_pre_topc(X1_44,sK2) != iProver_top
% 2.37/0.99      | m1_pre_topc(X0_44,sK2) != iProver_top
% 2.37/0.99      | v2_struct_0(X1_44) = iProver_top
% 2.37/0.99      | v2_struct_0(X0_44) = iProver_top ),
% 2.37/0.99      inference(predicate_to_equality,[status(thm)],[c_1514]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_3416,plain,
% 2.37/0.99      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK3,sK4)
% 2.37/0.99      | m1_pre_topc(sK3,sK2) != iProver_top
% 2.37/0.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 2.37/0.99      | v2_struct_0(sK3) = iProver_top
% 2.37/0.99      | v2_struct_0(sK4) = iProver_top ),
% 2.37/0.99      inference(superposition,[status(thm)],[c_1813,c_1823]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_2352,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(sK3,X0_44)
% 2.37/0.99      | ~ m1_pre_topc(sK3,sK2)
% 2.37/0.99      | v2_struct_0(X0_44)
% 2.37/0.99      | v2_struct_0(sK3)
% 2.37/0.99      | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK3,X0_44) ),
% 2.37/0.99      inference(instantiation,[status(thm)],[c_1514]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_2585,plain,
% 2.37/0.99      ( ~ m1_pre_topc(sK3,sK4)
% 2.37/0.99      | ~ m1_pre_topc(sK3,sK2)
% 2.37/0.99      | ~ m1_pre_topc(sK4,sK2)
% 2.37/0.99      | v2_struct_0(sK3)
% 2.37/0.99      | v2_struct_0(sK4)
% 2.37/0.99      | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK3,sK4) ),
% 2.37/0.99      inference(instantiation,[status(thm)],[c_2352]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_3686,plain,
% 2.37/0.99      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK3,sK4) ),
% 2.37/0.99      inference(global_propositional_subsumption,
% 2.37/0.99                [status(thm)],
% 2.37/0.99                [c_3416,c_32,c_31,c_30,c_29,c_26,c_2585]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_3932,plain,
% 2.37/0.99      ( k2_tsep_1(sK2,sK4,sK3) = k2_tsep_1(sK2,sK3,sK4)
% 2.37/0.99      | m1_pre_topc(sK3,sK2) != iProver_top
% 2.37/0.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 2.37/0.99      | v2_struct_0(sK3) = iProver_top
% 2.37/0.99      | v2_struct_0(sK4) = iProver_top ),
% 2.37/0.99      inference(demodulation,[status(thm)],[c_3892,c_3686]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_4028,plain,
% 2.37/0.99      ( k2_tsep_1(sK2,sK4,sK3) = k2_tsep_1(sK2,sK3,sK4) ),
% 2.37/0.99      inference(global_propositional_subsumption,
% 2.37/0.99                [status(thm)],
% 2.37/0.99                [c_3932,c_39,c_40,c_41,c_42]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_24,negated_conjecture,
% 2.37/0.99      ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
% 2.37/0.99      | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
% 2.37/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1526,negated_conjecture,
% 2.37/0.99      ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
% 2.37/0.99      | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
% 2.37/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_3689,plain,
% 2.37/0.99      ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) != k2_tsep_1(sK2,sK3,sK4)
% 2.37/0.99      | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) != k2_tsep_1(sK2,sK3,sK4) ),
% 2.37/0.99      inference(demodulation,[status(thm)],[c_3686,c_1526]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_4033,plain,
% 2.37/0.99      ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) != k2_tsep_1(sK2,sK4,sK3)
% 2.37/0.99      | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) != k2_tsep_1(sK2,sK4,sK3) ),
% 2.37/0.99      inference(demodulation,[status(thm)],[c_4028,c_3689]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_10,plain,
% 2.37/0.99      ( ~ sP0(X0,X1,X2,X3)
% 2.37/0.99      | ~ r1_tsep_1(X3,X1)
% 2.37/0.99      | r1_tsep_1(X3,X0)
% 2.37/0.99      | k2_tsep_1(X2,X3,k1_tsep_1(X2,X1,X0)) = k2_tsep_1(X2,X3,X0) ),
% 2.37/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_19,plain,
% 2.37/0.99      ( sP0(X0,X1,X2,X3)
% 2.37/0.99      | ~ m1_pre_topc(X3,X2)
% 2.37/0.99      | ~ m1_pre_topc(X1,X2)
% 2.37/0.99      | ~ m1_pre_topc(X0,X2)
% 2.37/0.99      | ~ v2_pre_topc(X2)
% 2.37/0.99      | ~ l1_pre_topc(X2)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X3)
% 2.37/0.99      | v2_struct_0(X0) ),
% 2.37/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_344,plain,
% 2.37/0.99      ( sP0(X0,X1,X2,X3)
% 2.37/0.99      | ~ m1_pre_topc(X0,X2)
% 2.37/0.99      | ~ m1_pre_topc(X1,X2)
% 2.37/0.99      | ~ m1_pre_topc(X3,X2)
% 2.37/0.99      | ~ v2_pre_topc(X2)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(X3)
% 2.37/0.99      | sK2 != X2 ),
% 2.37/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_33]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_345,plain,
% 2.37/0.99      ( sP0(X0,X1,sK2,X2)
% 2.37/0.99      | ~ m1_pre_topc(X2,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | ~ v2_pre_topc(sK2)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | v2_struct_0(sK2) ),
% 2.37/0.99      inference(unflattening,[status(thm)],[c_344]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_349,plain,
% 2.37/0.99      ( v2_struct_0(X2)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | sP0(X0,X1,sK2,X2)
% 2.37/0.99      | ~ m1_pre_topc(X2,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X0,sK2) ),
% 2.37/0.99      inference(global_propositional_subsumption,
% 2.37/0.99                [status(thm)],
% 2.37/0.99                [c_345,c_35,c_34]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_350,plain,
% 2.37/0.99      ( sP0(X0,X1,sK2,X2)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X2,sK2)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X0) ),
% 2.37/0.99      inference(renaming,[status(thm)],[c_349]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1186,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X2,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X3,X4)
% 2.37/0.99      | r1_tsep_1(X3,X5)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | X2 != X3
% 2.37/0.99      | X0 != X4
% 2.37/0.99      | X1 != X5
% 2.37/0.99      | k2_tsep_1(X6,X3,k1_tsep_1(X6,X4,X5)) = k2_tsep_1(X6,X3,X5)
% 2.37/0.99      | sK2 != X6 ),
% 2.37/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_350]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1187,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X2,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X0,X2)
% 2.37/0.99      | r1_tsep_1(X0,X1)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | k2_tsep_1(sK2,X0,k1_tsep_1(sK2,X2,X1)) = k2_tsep_1(sK2,X0,X1) ),
% 2.37/0.99      inference(unflattening,[status(thm)],[c_1186]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1495,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X2_44,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X0_44,X2_44)
% 2.37/0.99      | r1_tsep_1(X0_44,X1_44)
% 2.37/0.99      | v2_struct_0(X0_44)
% 2.37/0.99      | v2_struct_0(X1_44)
% 2.37/0.99      | v2_struct_0(X2_44)
% 2.37/0.99      | k2_tsep_1(sK2,X0_44,k1_tsep_1(sK2,X2_44,X1_44)) = k2_tsep_1(sK2,X0_44,X1_44) ),
% 2.37/0.99      inference(subtyping,[status(esa)],[c_1187]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_2378,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(sK4,sK2)
% 2.37/0.99      | ~ r1_tsep_1(sK4,X1_44)
% 2.37/0.99      | r1_tsep_1(sK4,X0_44)
% 2.37/0.99      | v2_struct_0(X0_44)
% 2.37/0.99      | v2_struct_0(X1_44)
% 2.37/0.99      | v2_struct_0(sK4)
% 2.37/0.99      | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,X1_44,X0_44)) = k2_tsep_1(sK2,sK4,X0_44) ),
% 2.37/0.99      inference(instantiation,[status(thm)],[c_1495]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_2622,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(sK3,sK2)
% 2.37/0.99      | ~ m1_pre_topc(sK4,sK2)
% 2.37/0.99      | ~ r1_tsep_1(sK4,X0_44)
% 2.37/0.99      | r1_tsep_1(sK4,sK3)
% 2.37/0.99      | v2_struct_0(X0_44)
% 2.37/0.99      | v2_struct_0(sK3)
% 2.37/0.99      | v2_struct_0(sK4)
% 2.37/0.99      | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,X0_44,sK3)) = k2_tsep_1(sK2,sK4,sK3) ),
% 2.37/0.99      inference(instantiation,[status(thm)],[c_2378]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_3181,plain,
% 2.37/0.99      ( ~ m1_pre_topc(sK3,sK2)
% 2.37/0.99      | ~ m1_pre_topc(sK5,sK2)
% 2.37/0.99      | ~ m1_pre_topc(sK4,sK2)
% 2.37/0.99      | r1_tsep_1(sK4,sK3)
% 2.37/0.99      | ~ r1_tsep_1(sK4,sK5)
% 2.37/0.99      | v2_struct_0(sK3)
% 2.37/0.99      | v2_struct_0(sK5)
% 2.37/0.99      | v2_struct_0(sK4)
% 2.37/0.99      | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) = k2_tsep_1(sK2,sK4,sK3) ),
% 2.37/0.99      inference(instantiation,[status(thm)],[c_2622]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_11,plain,
% 2.37/0.99      ( ~ sP0(X0,X1,X2,X3)
% 2.37/0.99      | ~ r1_tsep_1(X1,X3)
% 2.37/0.99      | r1_tsep_1(X3,X0)
% 2.37/0.99      | k2_tsep_1(X2,X3,k1_tsep_1(X2,X1,X0)) = k2_tsep_1(X2,X3,X0) ),
% 2.37/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1155,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X2,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X3,X4)
% 2.37/0.99      | r1_tsep_1(X4,X5)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | X2 != X4
% 2.37/0.99      | X0 != X3
% 2.37/0.99      | X1 != X5
% 2.37/0.99      | k2_tsep_1(X6,X4,k1_tsep_1(X6,X3,X5)) = k2_tsep_1(X6,X4,X5)
% 2.37/0.99      | sK2 != X6 ),
% 2.37/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_350]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1156,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X2,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X0,X2)
% 2.37/0.99      | r1_tsep_1(X2,X1)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | k2_tsep_1(sK2,X2,k1_tsep_1(sK2,X0,X1)) = k2_tsep_1(sK2,X2,X1) ),
% 2.37/0.99      inference(unflattening,[status(thm)],[c_1155]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1496,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X2_44,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X0_44,X2_44)
% 2.37/0.99      | r1_tsep_1(X2_44,X1_44)
% 2.37/0.99      | v2_struct_0(X0_44)
% 2.37/0.99      | v2_struct_0(X1_44)
% 2.37/0.99      | v2_struct_0(X2_44)
% 2.37/0.99      | k2_tsep_1(sK2,X2_44,k1_tsep_1(sK2,X0_44,X1_44)) = k2_tsep_1(sK2,X2_44,X1_44) ),
% 2.37/0.99      inference(subtyping,[status(esa)],[c_1156]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_2384,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(sK5,sK2)
% 2.37/0.99      | r1_tsep_1(X1_44,X0_44)
% 2.37/0.99      | ~ r1_tsep_1(sK5,X1_44)
% 2.37/0.99      | v2_struct_0(X0_44)
% 2.37/0.99      | v2_struct_0(X1_44)
% 2.37/0.99      | v2_struct_0(sK5)
% 2.37/0.99      | k2_tsep_1(sK2,X1_44,k1_tsep_1(sK2,sK5,X0_44)) = k2_tsep_1(sK2,X1_44,X0_44) ),
% 2.37/0.99      inference(instantiation,[status(thm)],[c_1496]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_2743,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(sK3,sK2)
% 2.37/0.99      | ~ m1_pre_topc(sK5,sK2)
% 2.37/0.99      | r1_tsep_1(X0_44,sK3)
% 2.37/0.99      | ~ r1_tsep_1(sK5,X0_44)
% 2.37/0.99      | v2_struct_0(X0_44)
% 2.37/0.99      | v2_struct_0(sK3)
% 2.37/0.99      | v2_struct_0(sK5)
% 2.37/0.99      | k2_tsep_1(sK2,X0_44,k1_tsep_1(sK2,sK5,sK3)) = k2_tsep_1(sK2,X0_44,sK3) ),
% 2.37/0.99      inference(instantiation,[status(thm)],[c_2384]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_3537,plain,
% 2.37/0.99      ( ~ m1_pre_topc(sK3,sK2)
% 2.37/0.99      | ~ m1_pre_topc(sK5,sK2)
% 2.37/0.99      | ~ m1_pre_topc(sK4,sK2)
% 2.37/0.99      | ~ r1_tsep_1(sK5,sK4)
% 2.37/0.99      | r1_tsep_1(sK4,sK3)
% 2.37/0.99      | v2_struct_0(sK3)
% 2.37/0.99      | v2_struct_0(sK5)
% 2.37/0.99      | v2_struct_0(sK4)
% 2.37/0.99      | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) = k2_tsep_1(sK2,sK4,sK3) ),
% 2.37/0.99      inference(instantiation,[status(thm)],[c_2743]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_4057,plain,
% 2.37/0.99      ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) != k2_tsep_1(sK2,sK4,sK3) ),
% 2.37/0.99      inference(global_propositional_subsumption,
% 2.37/0.99                [status(thm)],
% 2.37/0.99                [c_4033,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_25,c_2508,
% 2.37/0.99                 c_3181,c_3537]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_2,plain,
% 2.37/0.99      ( ~ sP1(X0,X1,X2,X3)
% 2.37/0.99      | ~ r1_tsep_1(X3,X0)
% 2.37/0.99      | r1_tsep_1(X3,X1)
% 2.37/0.99      | k2_tsep_1(X2,X3,k1_tsep_1(X2,X1,X0)) = k2_tsep_1(X2,X3,X1) ),
% 2.37/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_858,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X2,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X3,X4)
% 2.37/0.99      | r1_tsep_1(X3,X5)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | X2 != X3
% 2.37/0.99      | X0 != X5
% 2.37/0.99      | X1 != X4
% 2.37/0.99      | k2_tsep_1(X6,X3,k1_tsep_1(X6,X5,X4)) = k2_tsep_1(X6,X3,X5)
% 2.37/0.99      | sK2 != X6 ),
% 2.37/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_383]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_859,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X2,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X0,X2)
% 2.37/0.99      | r1_tsep_1(X0,X1)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | k2_tsep_1(sK2,X0,k1_tsep_1(sK2,X1,X2)) = k2_tsep_1(sK2,X0,X1) ),
% 2.37/0.99      inference(unflattening,[status(thm)],[c_858]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1503,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X2_44,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X0_44,X2_44)
% 2.37/0.99      | r1_tsep_1(X0_44,X1_44)
% 2.37/0.99      | v2_struct_0(X0_44)
% 2.37/0.99      | v2_struct_0(X1_44)
% 2.37/0.99      | v2_struct_0(X2_44)
% 2.37/0.99      | k2_tsep_1(sK2,X0_44,k1_tsep_1(sK2,X1_44,X2_44)) = k2_tsep_1(sK2,X0_44,X1_44) ),
% 2.37/0.99      inference(subtyping,[status(esa)],[c_859]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_3104,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(sK4,sK2)
% 2.37/0.99      | ~ r1_tsep_1(sK4,X1_44)
% 2.37/0.99      | r1_tsep_1(sK4,X0_44)
% 2.37/0.99      | v2_struct_0(X0_44)
% 2.37/0.99      | v2_struct_0(X1_44)
% 2.37/0.99      | v2_struct_0(sK4)
% 2.37/0.99      | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,X0_44,X1_44)) = k2_tsep_1(sK2,sK4,X0_44) ),
% 2.37/0.99      inference(instantiation,[status(thm)],[c_1503]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_4009,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(sK3,sK2)
% 2.37/0.99      | ~ m1_pre_topc(sK4,sK2)
% 2.37/0.99      | ~ r1_tsep_1(sK4,X0_44)
% 2.37/0.99      | r1_tsep_1(sK4,sK3)
% 2.37/0.99      | v2_struct_0(X0_44)
% 2.37/0.99      | v2_struct_0(sK3)
% 2.37/0.99      | v2_struct_0(sK4)
% 2.37/0.99      | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,X0_44)) = k2_tsep_1(sK2,sK4,sK3) ),
% 2.37/0.99      inference(instantiation,[status(thm)],[c_3104]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_4412,plain,
% 2.37/0.99      ( ~ m1_pre_topc(sK3,sK2)
% 2.37/0.99      | ~ m1_pre_topc(sK5,sK2)
% 2.37/0.99      | ~ m1_pre_topc(sK4,sK2)
% 2.37/0.99      | r1_tsep_1(sK4,sK3)
% 2.37/0.99      | ~ r1_tsep_1(sK4,sK5)
% 2.37/0.99      | v2_struct_0(sK3)
% 2.37/0.99      | v2_struct_0(sK5)
% 2.37/0.99      | v2_struct_0(sK4)
% 2.37/0.99      | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) = k2_tsep_1(sK2,sK4,sK3) ),
% 2.37/0.99      inference(instantiation,[status(thm)],[c_4009]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_4413,plain,
% 2.37/0.99      ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) = k2_tsep_1(sK2,sK4,sK3)
% 2.37/0.99      | m1_pre_topc(sK3,sK2) != iProver_top
% 2.37/0.99      | m1_pre_topc(sK5,sK2) != iProver_top
% 2.37/0.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 2.37/0.99      | r1_tsep_1(sK4,sK3) = iProver_top
% 2.37/0.99      | r1_tsep_1(sK4,sK5) != iProver_top
% 2.37/0.99      | v2_struct_0(sK3) = iProver_top
% 2.37/0.99      | v2_struct_0(sK5) = iProver_top
% 2.37/0.99      | v2_struct_0(sK4) = iProver_top ),
% 2.37/0.99      inference(predicate_to_equality,[status(thm)],[c_4412]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_4647,plain,
% 2.37/0.99      ( r1_tsep_1(X0_44,sK5) = iProver_top
% 2.37/0.99      | m1_pre_topc(X0_44,sK2) != iProver_top
% 2.37/0.99      | k2_tsep_1(sK2,k1_tsep_1(sK2,X0_44,sK4),sK5) = k2_tsep_1(sK2,X0_44,sK5)
% 2.37/0.99      | v2_struct_0(X0_44) = iProver_top ),
% 2.37/0.99      inference(global_propositional_subsumption,
% 2.37/0.99                [status(thm)],
% 2.37/0.99                [c_4463,c_32,c_39,c_31,c_40,c_30,c_41,c_29,c_42,c_28,
% 2.37/0.99                 c_43,c_27,c_44,c_26,c_45,c_25,c_2508,c_2509,c_3181,
% 2.37/0.99                 c_3537,c_4033,c_4413]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_4648,plain,
% 2.37/0.99      ( k2_tsep_1(sK2,k1_tsep_1(sK2,X0_44,sK4),sK5) = k2_tsep_1(sK2,X0_44,sK5)
% 2.37/0.99      | m1_pre_topc(X0_44,sK2) != iProver_top
% 2.37/0.99      | r1_tsep_1(X0_44,sK5) = iProver_top
% 2.37/0.99      | v2_struct_0(X0_44) = iProver_top ),
% 2.37/0.99      inference(renaming,[status(thm)],[c_4647]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_4657,plain,
% 2.37/0.99      ( k2_tsep_1(sK2,k1_tsep_1(sK2,sK5,sK4),sK5) = k2_tsep_1(sK2,sK5,sK5)
% 2.37/0.99      | r1_tsep_1(sK5,sK5) = iProver_top
% 2.37/0.99      | v2_struct_0(sK5) = iProver_top ),
% 2.37/0.99      inference(superposition,[status(thm)],[c_1814,c_4648]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_4682,plain,
% 2.37/0.99      ( r1_tsep_1(sK5,sK5) = iProver_top
% 2.37/0.99      | k2_tsep_1(sK2,k1_tsep_1(sK2,sK5,sK4),sK5) = k2_tsep_1(sK2,sK5,sK5) ),
% 2.37/0.99      inference(global_propositional_subsumption,
% 2.37/0.99                [status(thm)],
% 2.37/0.99                [c_4657,c_43]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_4683,plain,
% 2.37/0.99      ( k2_tsep_1(sK2,k1_tsep_1(sK2,sK5,sK4),sK5) = k2_tsep_1(sK2,sK5,sK5)
% 2.37/0.99      | r1_tsep_1(sK5,sK5) = iProver_top ),
% 2.37/0.99      inference(renaming,[status(thm)],[c_4682]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_8,plain,
% 2.37/0.99      ( ~ sP1(X0,X1,X2,X3)
% 2.37/0.99      | ~ r1_tsep_1(X0,X3)
% 2.37/0.99      | r1_tsep_1(X3,X1)
% 2.37/0.99      | k2_tsep_1(X2,k1_tsep_1(X2,X1,X0),X3) = k2_tsep_1(X2,X1,X3) ),
% 2.37/0.99      inference(cnf_transformation,[],[f29]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_672,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X2,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X3,X4)
% 2.37/0.99      | r1_tsep_1(X4,X5)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | X2 != X4
% 2.37/0.99      | X0 != X5
% 2.37/0.99      | X1 != X3
% 2.37/0.99      | k2_tsep_1(X6,k1_tsep_1(X6,X5,X3),X4) = k2_tsep_1(X6,X5,X4)
% 2.37/0.99      | sK2 != X6 ),
% 2.37/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_383]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_673,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X2,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X0,X2)
% 2.37/0.99      | r1_tsep_1(X2,X1)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | k2_tsep_1(sK2,k1_tsep_1(sK2,X1,X0),X2) = k2_tsep_1(sK2,X1,X2) ),
% 2.37/0.99      inference(unflattening,[status(thm)],[c_672]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1509,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X2_44,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X0_44,X2_44)
% 2.37/0.99      | r1_tsep_1(X2_44,X1_44)
% 2.37/0.99      | v2_struct_0(X0_44)
% 2.37/0.99      | v2_struct_0(X1_44)
% 2.37/0.99      | v2_struct_0(X2_44)
% 2.37/0.99      | k2_tsep_1(sK2,k1_tsep_1(sK2,X1_44,X0_44),X2_44) = k2_tsep_1(sK2,X1_44,X2_44) ),
% 2.37/0.99      inference(subtyping,[status(esa)],[c_673]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1828,plain,
% 2.37/0.99      ( k2_tsep_1(sK2,k1_tsep_1(sK2,X0_44,X1_44),X2_44) = k2_tsep_1(sK2,X0_44,X2_44)
% 2.37/0.99      | m1_pre_topc(X2_44,sK2) != iProver_top
% 2.37/0.99      | m1_pre_topc(X0_44,sK2) != iProver_top
% 2.37/0.99      | m1_pre_topc(X1_44,sK2) != iProver_top
% 2.37/0.99      | r1_tsep_1(X1_44,X2_44) != iProver_top
% 2.37/0.99      | r1_tsep_1(X2_44,X0_44) = iProver_top
% 2.37/0.99      | v2_struct_0(X0_44) = iProver_top
% 2.37/0.99      | v2_struct_0(X1_44) = iProver_top
% 2.37/0.99      | v2_struct_0(X2_44) = iProver_top ),
% 2.37/0.99      inference(predicate_to_equality,[status(thm)],[c_1509]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_4689,plain,
% 2.37/0.99      ( k2_tsep_1(sK2,k1_tsep_1(sK2,X0_44,sK5),sK5) = k2_tsep_1(sK2,X0_44,sK5)
% 2.37/0.99      | k2_tsep_1(sK2,k1_tsep_1(sK2,sK5,sK4),sK5) = k2_tsep_1(sK2,sK5,sK5)
% 2.37/0.99      | m1_pre_topc(X0_44,sK2) != iProver_top
% 2.37/0.99      | m1_pre_topc(sK5,sK2) != iProver_top
% 2.37/0.99      | r1_tsep_1(sK5,X0_44) = iProver_top
% 2.37/0.99      | v2_struct_0(X0_44) = iProver_top
% 2.37/0.99      | v2_struct_0(sK5) = iProver_top ),
% 2.37/0.99      inference(superposition,[status(thm)],[c_4683,c_1828]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_5006,plain,
% 2.37/0.99      ( v2_struct_0(X0_44) = iProver_top
% 2.37/0.99      | r1_tsep_1(sK5,X0_44) = iProver_top
% 2.37/0.99      | k2_tsep_1(sK2,k1_tsep_1(sK2,X0_44,sK5),sK5) = k2_tsep_1(sK2,X0_44,sK5)
% 2.37/0.99      | k2_tsep_1(sK2,k1_tsep_1(sK2,sK5,sK4),sK5) = k2_tsep_1(sK2,sK5,sK5)
% 2.37/0.99      | m1_pre_topc(X0_44,sK2) != iProver_top ),
% 2.37/0.99      inference(global_propositional_subsumption,
% 2.37/0.99                [status(thm)],
% 2.37/0.99                [c_4689,c_43,c_44]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_5007,plain,
% 2.37/0.99      ( k2_tsep_1(sK2,k1_tsep_1(sK2,X0_44,sK5),sK5) = k2_tsep_1(sK2,X0_44,sK5)
% 2.37/0.99      | k2_tsep_1(sK2,k1_tsep_1(sK2,sK5,sK4),sK5) = k2_tsep_1(sK2,sK5,sK5)
% 2.37/0.99      | m1_pre_topc(X0_44,sK2) != iProver_top
% 2.37/0.99      | r1_tsep_1(sK5,X0_44) = iProver_top
% 2.37/0.99      | v2_struct_0(X0_44) = iProver_top ),
% 2.37/0.99      inference(renaming,[status(thm)],[c_5006]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_5018,plain,
% 2.37/0.99      ( k2_tsep_1(sK2,k1_tsep_1(sK2,sK5,sK4),sK5) = k2_tsep_1(sK2,sK5,sK5)
% 2.37/0.99      | k2_tsep_1(sK2,k1_tsep_1(sK2,sK4,sK5),sK5) = k2_tsep_1(sK2,sK4,sK5)
% 2.37/0.99      | r1_tsep_1(sK5,sK4) = iProver_top
% 2.37/0.99      | v2_struct_0(sK4) = iProver_top ),
% 2.37/0.99      inference(superposition,[status(thm)],[c_1816,c_5007]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_46,plain,
% 2.37/0.99      ( r1_tsep_1(sK5,sK4) = iProver_top
% 2.37/0.99      | r1_tsep_1(sK4,sK5) = iProver_top ),
% 2.37/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_5039,plain,
% 2.37/0.99      ( r1_tsep_1(sK5,sK4) = iProver_top ),
% 2.37/0.99      inference(global_propositional_subsumption,
% 2.37/0.99                [status(thm)],
% 2.37/0.99                [c_5018,c_32,c_39,c_31,c_40,c_30,c_41,c_29,c_42,c_28,
% 2.37/0.99                 c_43,c_27,c_44,c_26,c_45,c_25,c_46,c_2508,c_2509,c_3181,
% 2.37/0.99                 c_3537,c_4033,c_4413]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_5,plain,
% 2.37/0.99      ( ~ sP1(X0,X1,X2,X3)
% 2.37/0.99      | ~ r1_tsep_1(X0,X3)
% 2.37/0.99      | r1_tsep_1(X1,X3)
% 2.37/0.99      | k2_tsep_1(X2,X3,k1_tsep_1(X2,X1,X0)) = k2_tsep_1(X2,X3,X1) ),
% 2.37/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_765,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X2,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X3,X4)
% 2.37/0.99      | r1_tsep_1(X5,X4)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | X2 != X4
% 2.37/0.99      | X0 != X5
% 2.37/0.99      | X1 != X3
% 2.37/0.99      | k2_tsep_1(X6,X4,k1_tsep_1(X6,X5,X3)) = k2_tsep_1(X6,X4,X5)
% 2.37/0.99      | sK2 != X6 ),
% 2.37/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_383]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_766,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X2,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X0,X2)
% 2.37/0.99      | r1_tsep_1(X1,X2)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | k2_tsep_1(sK2,X2,k1_tsep_1(sK2,X1,X0)) = k2_tsep_1(sK2,X2,X1) ),
% 2.37/0.99      inference(unflattening,[status(thm)],[c_765]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1506,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X2_44,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X0_44,X2_44)
% 2.37/0.99      | r1_tsep_1(X1_44,X2_44)
% 2.37/0.99      | v2_struct_0(X0_44)
% 2.37/0.99      | v2_struct_0(X1_44)
% 2.37/0.99      | v2_struct_0(X2_44)
% 2.37/0.99      | k2_tsep_1(sK2,X2_44,k1_tsep_1(sK2,X1_44,X0_44)) = k2_tsep_1(sK2,X2_44,X1_44) ),
% 2.37/0.99      inference(subtyping,[status(esa)],[c_766]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1831,plain,
% 2.37/0.99      ( k2_tsep_1(sK2,X0_44,k1_tsep_1(sK2,X1_44,X2_44)) = k2_tsep_1(sK2,X0_44,X1_44)
% 2.37/0.99      | m1_pre_topc(X0_44,sK2) != iProver_top
% 2.37/0.99      | m1_pre_topc(X1_44,sK2) != iProver_top
% 2.37/0.99      | m1_pre_topc(X2_44,sK2) != iProver_top
% 2.37/0.99      | r1_tsep_1(X2_44,X0_44) != iProver_top
% 2.37/0.99      | r1_tsep_1(X1_44,X0_44) = iProver_top
% 2.37/0.99      | v2_struct_0(X1_44) = iProver_top
% 2.37/0.99      | v2_struct_0(X2_44) = iProver_top
% 2.37/0.99      | v2_struct_0(X0_44) = iProver_top ),
% 2.37/0.99      inference(predicate_to_equality,[status(thm)],[c_1506]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_5570,plain,
% 2.37/0.99      ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,X0_44,sK5)) = k2_tsep_1(sK2,sK4,X0_44)
% 2.37/0.99      | m1_pre_topc(X0_44,sK2) != iProver_top
% 2.37/0.99      | m1_pre_topc(sK5,sK2) != iProver_top
% 2.37/0.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 2.37/0.99      | r1_tsep_1(X0_44,sK4) = iProver_top
% 2.37/0.99      | v2_struct_0(X0_44) = iProver_top
% 2.37/0.99      | v2_struct_0(sK5) = iProver_top
% 2.37/0.99      | v2_struct_0(sK4) = iProver_top ),
% 2.37/0.99      inference(superposition,[status(thm)],[c_5039,c_1831]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_6075,plain,
% 2.37/0.99      ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,X0_44,sK5)) = k2_tsep_1(sK2,sK4,X0_44)
% 2.37/0.99      | m1_pre_topc(X0_44,sK2) != iProver_top
% 2.37/0.99      | r1_tsep_1(X0_44,sK4) = iProver_top
% 2.37/0.99      | v2_struct_0(X0_44) = iProver_top ),
% 2.37/0.99      inference(global_propositional_subsumption,
% 2.37/0.99                [status(thm)],
% 2.37/0.99                [c_5570,c_41,c_42,c_43,c_44]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_6087,plain,
% 2.37/0.99      ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) = k2_tsep_1(sK2,sK4,sK3)
% 2.37/0.99      | r1_tsep_1(sK3,sK4) = iProver_top
% 2.37/0.99      | v2_struct_0(sK3) = iProver_top ),
% 2.37/0.99      inference(superposition,[status(thm)],[c_1818,c_6075]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_410,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | ~ m1_pre_topc(X2,X1)
% 2.37/0.99      | ~ m1_pre_topc(X0,X2)
% 2.37/0.99      | ~ r1_tsep_1(X0,X2)
% 2.37/0.99      | ~ v2_pre_topc(X1)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X2)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | sK2 != X1 ),
% 2.37/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_33]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_411,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X0,X1)
% 2.37/0.99      | ~ v2_pre_topc(sK2)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(sK2) ),
% 2.37/0.99      inference(unflattening,[status(thm)],[c_410]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_415,plain,
% 2.37/0.99      ( v2_struct_0(X0)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X0,X1) ),
% 2.37/0.99      inference(global_propositional_subsumption,
% 2.37/0.99                [status(thm)],
% 2.37/0.99                [c_411,c_35,c_34]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_416,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.37/0.99      | ~ m1_pre_topc(X1,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X0,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X0,X1)
% 2.37/0.99      | v2_struct_0(X1)
% 2.37/0.99      | v2_struct_0(X0) ),
% 2.37/0.99      inference(renaming,[status(thm)],[c_415]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_1516,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0_44,X1_44)
% 2.37/0.99      | ~ m1_pre_topc(X0_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(X1_44,sK2)
% 2.37/0.99      | ~ r1_tsep_1(X0_44,X1_44)
% 2.37/0.99      | v2_struct_0(X0_44)
% 2.37/0.99      | v2_struct_0(X1_44) ),
% 2.37/0.99      inference(subtyping,[status(esa)],[c_416]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_2322,plain,
% 2.37/0.99      ( ~ m1_pre_topc(X0_44,sK2)
% 2.37/0.99      | ~ m1_pre_topc(sK3,X0_44)
% 2.37/0.99      | ~ m1_pre_topc(sK3,sK2)
% 2.37/0.99      | ~ r1_tsep_1(sK3,X0_44)
% 2.37/0.99      | v2_struct_0(X0_44)
% 2.37/0.99      | v2_struct_0(sK3) ),
% 2.37/0.99      inference(instantiation,[status(thm)],[c_1516]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_2533,plain,
% 2.37/0.99      ( ~ m1_pre_topc(sK3,sK4)
% 2.37/0.99      | ~ m1_pre_topc(sK3,sK2)
% 2.37/0.99      | ~ m1_pre_topc(sK4,sK2)
% 2.37/0.99      | ~ r1_tsep_1(sK3,sK4)
% 2.37/0.99      | v2_struct_0(sK3)
% 2.37/0.99      | v2_struct_0(sK4) ),
% 2.37/0.99      inference(instantiation,[status(thm)],[c_2322]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(c_2534,plain,
% 2.37/0.99      ( m1_pre_topc(sK3,sK4) != iProver_top
% 2.37/0.99      | m1_pre_topc(sK3,sK2) != iProver_top
% 2.37/0.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 2.37/0.99      | r1_tsep_1(sK3,sK4) != iProver_top
% 2.37/0.99      | v2_struct_0(sK3) = iProver_top
% 2.37/0.99      | v2_struct_0(sK4) = iProver_top ),
% 2.37/0.99      inference(predicate_to_equality,[status(thm)],[c_2533]) ).
% 2.37/0.99  
% 2.37/0.99  cnf(contradiction,plain,
% 2.37/0.99      ( $false ),
% 2.37/0.99      inference(minisat,
% 2.37/0.99                [status(thm)],
% 2.37/0.99                [c_6087,c_4057,c_2534,c_45,c_42,c_41,c_40,c_39]) ).
% 2.37/0.99  
% 2.37/0.99  
% 2.37/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.37/0.99  
% 2.37/0.99  ------                               Statistics
% 2.37/0.99  
% 2.37/0.99  ------ General
% 2.37/0.99  
% 2.37/0.99  abstr_ref_over_cycles:                  0
% 2.37/0.99  abstr_ref_under_cycles:                 0
% 2.37/0.99  gc_basic_clause_elim:                   0
% 2.37/0.99  forced_gc_time:                         0
% 2.37/0.99  parsing_time:                           0.01
% 2.37/0.99  unif_index_cands_time:                  0.
% 2.37/0.99  unif_index_add_time:                    0.
% 2.37/0.99  orderings_time:                         0.
% 2.37/0.99  out_proof_time:                         0.013
% 2.37/0.99  total_time:                             0.211
% 2.37/0.99  num_of_symbols:                         48
% 2.37/0.99  num_of_terms:                           1955
% 2.37/0.99  
% 2.37/0.99  ------ Preprocessing
% 2.37/0.99  
% 2.37/0.99  num_of_splits:                          0
% 2.37/0.99  num_of_split_atoms:                     0
% 2.37/0.99  num_of_reused_defs:                     0
% 2.37/0.99  num_eq_ax_congr_red:                    23
% 2.37/0.99  num_of_sem_filtered_clauses:            0
% 2.37/0.99  num_of_subtypes:                        4
% 2.37/0.99  monotx_restored_types:                  0
% 2.37/0.99  sat_num_of_epr_types:                   0
% 2.37/0.99  sat_num_of_non_cyclic_types:            0
% 2.37/0.99  sat_guarded_non_collapsed_types:        0
% 2.37/0.99  num_pure_diseq_elim:                    0
% 2.37/0.99  simp_replaced_by:                       0
% 2.37/0.99  res_preprocessed:                       102
% 2.37/0.99  prep_upred:                             0
% 2.37/0.99  prep_unflattend:                        72
% 2.37/0.99  smt_new_axioms:                         0
% 2.37/0.99  pred_elim_cands:                        3
% 2.37/0.99  pred_elim:                              4
% 2.37/0.99  pred_elim_cl:                           4
% 2.37/0.99  pred_elim_cycles:                       6
% 2.37/0.99  merged_defs:                            0
% 2.37/0.99  merged_defs_ncl:                        0
% 2.37/0.99  bin_hyper_res:                          0
% 2.37/0.99  prep_cycles:                            3
% 2.37/0.99  pred_elim_time:                         0.024
% 2.37/0.99  splitting_time:                         0.
% 2.37/0.99  sem_filter_time:                        0.
% 2.37/0.99  monotx_time:                            0.
% 2.37/0.99  subtype_inf_time:                       0.
% 2.37/0.99  
% 2.37/0.99  ------ Problem properties
% 2.37/0.99  
% 2.37/0.99  clauses:                                32
% 2.37/0.99  conjectures:                            10
% 2.37/0.99  epr:                                    11
% 2.37/0.99  horn:                                   9
% 2.37/0.99  ground:                                 10
% 2.37/0.99  unary:                                  8
% 2.37/0.99  binary:                                 2
% 2.37/0.99  lits:                                   194
% 2.37/0.99  lits_eq:                                22
% 2.37/0.99  fd_pure:                                0
% 2.37/0.99  fd_pseudo:                              0
% 2.37/0.99  fd_cond:                                0
% 2.37/0.99  fd_pseudo_cond:                         0
% 2.37/0.99  ac_symbols:                             0
% 2.37/0.99  
% 2.37/0.99  ------ Propositional Solver
% 2.37/0.99  
% 2.37/0.99  prop_solver_calls:                      22
% 2.37/0.99  prop_fast_solver_calls:                 1832
% 2.37/0.99  smt_solver_calls:                       0
% 2.37/0.99  smt_fast_solver_calls:                  0
% 2.37/0.99  prop_num_of_clauses:                    1425
% 2.37/0.99  prop_preprocess_simplified:             5061
% 2.37/0.99  prop_fo_subsumed:                       128
% 2.37/0.99  prop_solver_time:                       0.
% 2.37/0.99  smt_solver_time:                        0.
% 2.37/0.99  smt_fast_solver_time:                   0.
% 2.37/0.99  prop_fast_solver_time:                  0.
% 2.37/0.99  prop_unsat_core_time:                   0.
% 2.37/0.99  
% 2.37/0.99  ------ QBF
% 2.37/0.99  
% 2.37/0.99  qbf_q_res:                              0
% 2.37/0.99  qbf_num_tautologies:                    0
% 2.37/0.99  qbf_prep_cycles:                        0
% 2.37/0.99  
% 2.37/0.99  ------ BMC1
% 2.37/0.99  
% 2.37/0.99  bmc1_current_bound:                     -1
% 2.37/0.99  bmc1_last_solved_bound:                 -1
% 2.37/0.99  bmc1_unsat_core_size:                   -1
% 2.37/0.99  bmc1_unsat_core_parents_size:           -1
% 2.37/0.99  bmc1_merge_next_fun:                    0
% 2.37/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.37/0.99  
% 2.37/0.99  ------ Instantiation
% 2.37/0.99  
% 2.37/0.99  inst_num_of_clauses:                    414
% 2.37/0.99  inst_num_in_passive:                    103
% 2.37/0.99  inst_num_in_active:                     307
% 2.37/0.99  inst_num_in_unprocessed:                4
% 2.37/0.99  inst_num_of_loops:                      330
% 2.37/0.99  inst_num_of_learning_restarts:          0
% 2.37/0.99  inst_num_moves_active_passive:          21
% 2.37/0.99  inst_lit_activity:                      0
% 2.37/0.99  inst_lit_activity_moves:                0
% 2.37/0.99  inst_num_tautologies:                   0
% 2.37/0.99  inst_num_prop_implied:                  0
% 2.37/0.99  inst_num_existing_simplified:           0
% 2.37/0.99  inst_num_eq_res_simplified:             0
% 2.37/0.99  inst_num_child_elim:                    0
% 2.37/0.99  inst_num_of_dismatching_blockings:      3
% 2.37/0.99  inst_num_of_non_proper_insts:           399
% 2.37/0.99  inst_num_of_duplicates:                 0
% 2.37/0.99  inst_inst_num_from_inst_to_res:         0
% 2.37/0.99  inst_dismatching_checking_time:         0.
% 2.37/0.99  
% 2.37/0.99  ------ Resolution
% 2.37/0.99  
% 2.37/0.99  res_num_of_clauses:                     0
% 2.37/0.99  res_num_in_passive:                     0
% 2.37/0.99  res_num_in_active:                      0
% 2.37/0.99  res_num_of_loops:                       105
% 2.37/0.99  res_forward_subset_subsumed:            10
% 2.37/0.99  res_backward_subset_subsumed:           0
% 2.37/0.99  res_forward_subsumed:                   0
% 2.37/0.99  res_backward_subsumed:                  0
% 2.37/0.99  res_forward_subsumption_resolution:     0
% 2.37/0.99  res_backward_subsumption_resolution:    0
% 2.37/0.99  res_clause_to_clause_subsumption:       1728
% 2.37/0.99  res_orphan_elimination:                 0
% 2.37/0.99  res_tautology_del:                      90
% 2.37/0.99  res_num_eq_res_simplified:              0
% 2.37/0.99  res_num_sel_changes:                    0
% 2.37/0.99  res_moves_from_active_to_pass:          0
% 2.37/0.99  
% 2.37/0.99  ------ Superposition
% 2.37/0.99  
% 2.37/0.99  sup_time_total:                         0.
% 2.37/0.99  sup_time_generating:                    0.
% 2.37/0.99  sup_time_sim_full:                      0.
% 2.37/0.99  sup_time_sim_immed:                     0.
% 2.37/0.99  
% 2.37/0.99  sup_num_of_clauses:                     109
% 2.37/0.99  sup_num_in_active:                      57
% 2.37/0.99  sup_num_in_passive:                     52
% 2.37/0.99  sup_num_of_loops:                       64
% 2.37/0.99  sup_fw_superposition:                   85
% 2.37/0.99  sup_bw_superposition:                   33
% 2.37/0.99  sup_immediate_simplified:               21
% 2.37/0.99  sup_given_eliminated:                   0
% 2.37/0.99  comparisons_done:                       0
% 2.37/0.99  comparisons_avoided:                    6
% 2.37/0.99  
% 2.37/0.99  ------ Simplifications
% 2.37/0.99  
% 2.37/0.99  
% 2.37/0.99  sim_fw_subset_subsumed:                 9
% 2.37/0.99  sim_bw_subset_subsumed:                 2
% 2.37/0.99  sim_fw_subsumed:                        7
% 2.37/0.99  sim_bw_subsumed:                        0
% 2.37/0.99  sim_fw_subsumption_res:                 0
% 2.37/0.99  sim_bw_subsumption_res:                 0
% 2.37/0.99  sim_tautology_del:                      0
% 2.37/0.99  sim_eq_tautology_del:                   1
% 2.37/0.99  sim_eq_res_simp:                        0
% 2.37/0.99  sim_fw_demodulated:                     3
% 2.37/0.99  sim_bw_demodulated:                     6
% 2.37/0.99  sim_light_normalised:                   5
% 2.37/0.99  sim_joinable_taut:                      0
% 2.37/0.99  sim_joinable_simp:                      0
% 2.37/0.99  sim_ac_normalised:                      0
% 2.37/0.99  sim_smt_subsumption:                    0
% 2.37/0.99  
%------------------------------------------------------------------------------
