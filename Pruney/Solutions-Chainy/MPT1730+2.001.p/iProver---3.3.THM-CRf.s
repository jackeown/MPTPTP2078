%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:14 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  234 (2837 expanded)
%              Number of clauses        :  169 ( 745 expanded)
%              Number of leaves         :   16 ( 935 expanded)
%              Depth                    :   25
%              Number of atoms          : 1115 (32318 expanded)
%              Number of equality atoms :  221 ( 535 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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
                 => ( ~ ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                        & ~ ( r1_tsep_1(X3,X2)
                            & r1_tsep_1(X3,X1) ) )
                    & ~ ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1)
                        & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ~ ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                        & ~ ( r1_tsep_1(X2,X3)
                            & r1_tsep_1(X1,X3) ) )
                    & ~ ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3)
                        & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ),
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
                   => ( ~ ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                          & ~ ( r1_tsep_1(X3,X2)
                              & r1_tsep_1(X3,X1) ) )
                      & ~ ( r1_tsep_1(X3,X2)
                          & r1_tsep_1(X3,X1)
                          & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                      & ~ ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                          & ~ ( r1_tsep_1(X2,X3)
                              & r1_tsep_1(X1,X3) ) )
                      & ~ ( r1_tsep_1(X2,X3)
                          & r1_tsep_1(X1,X3)
                          & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ~ ! [X0] :
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
                      & ~ v2_struct_0(X3) )
                   => ( ~ ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                          & ~ ( r1_tsep_1(X3,X2)
                              & r1_tsep_1(X3,X1) ) )
                      & ~ ( r1_tsep_1(X3,X2)
                          & r1_tsep_1(X3,X1)
                          & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                      & ~ ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                          & ~ ( r1_tsep_1(X2,X3)
                              & r1_tsep_1(X1,X3) ) )
                      & ~ ( r1_tsep_1(X2,X3)
                          & r1_tsep_1(X1,X3)
                          & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) ) )
                    | ( r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1)
                      & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) ) )
                    | ( r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3)
                      & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) ) )
                    | ( r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1)
                      & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) ) )
                    | ( r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3)
                      & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f24,plain,(
    ! [X2,X3,X1,X0] :
      ( ( r1_tsep_1(X3,X2)
        & r1_tsep_1(X3,X1)
        & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
      | ~ sP1(X2,X3,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f23,plain,(
    ! [X3,X2,X1,X0] :
      ( ( r1_tsep_1(X2,X3)
        & r1_tsep_1(X1,X3)
        & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) ) )
                    | sP1(X2,X3,X1,X0)
                    | ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) ) )
                    | sP0(X3,X2,X1,X0) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f22,f24,f23])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
              & ( ~ r1_tsep_1(X3,X2)
                | ~ r1_tsep_1(X3,X1) ) )
            | sP1(X2,X3,X1,X0)
            | ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
              & ( ~ r1_tsep_1(X2,X3)
                | ~ r1_tsep_1(X1,X3) ) )
            | sP0(X3,X2,X1,X0) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ( ( r1_tsep_1(sK5,k1_tsep_1(X0,X1,X2))
            & ( ~ r1_tsep_1(sK5,X2)
              | ~ r1_tsep_1(sK5,X1) ) )
          | sP1(X2,sK5,X1,X0)
          | ( r1_tsep_1(k1_tsep_1(X0,X1,X2),sK5)
            & ( ~ r1_tsep_1(X2,sK5)
              | ~ r1_tsep_1(X1,sK5) ) )
          | sP0(sK5,X2,X1,X0) )
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                  & ( ~ r1_tsep_1(X3,X2)
                    | ~ r1_tsep_1(X3,X1) ) )
                | sP1(X2,X3,X1,X0)
                | ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                  & ( ~ r1_tsep_1(X2,X3)
                    | ~ r1_tsep_1(X1,X3) ) )
                | sP0(X3,X2,X1,X0) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,sK4))
                & ( ~ r1_tsep_1(X3,sK4)
                  | ~ r1_tsep_1(X3,X1) ) )
              | sP1(sK4,X3,X1,X0)
              | ( r1_tsep_1(k1_tsep_1(X0,X1,sK4),X3)
                & ( ~ r1_tsep_1(sK4,X3)
                  | ~ r1_tsep_1(X1,X3) ) )
              | sP0(X3,sK4,X1,X0) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) ) )
                    | sP1(X2,X3,X1,X0)
                    | ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) ) )
                    | sP0(X3,X2,X1,X0) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,sK3,X2))
                    & ( ~ r1_tsep_1(X3,X2)
                      | ~ r1_tsep_1(X3,sK3) ) )
                  | sP1(X2,X3,sK3,X0)
                  | ( r1_tsep_1(k1_tsep_1(X0,sK3,X2),X3)
                    & ( ~ r1_tsep_1(X2,X3)
                      | ~ r1_tsep_1(sK3,X3) ) )
                  | sP0(X3,X2,sK3,X0) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                        & ( ~ r1_tsep_1(X3,X2)
                          | ~ r1_tsep_1(X3,X1) ) )
                      | sP1(X2,X3,X1,X0)
                      | ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                        & ( ~ r1_tsep_1(X2,X3)
                          | ~ r1_tsep_1(X1,X3) ) )
                      | sP0(X3,X2,X1,X0) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( r1_tsep_1(X3,k1_tsep_1(sK2,X1,X2))
                      & ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) ) )
                    | sP1(X2,X3,X1,sK2)
                    | ( r1_tsep_1(k1_tsep_1(sK2,X1,X2),X3)
                      & ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) ) )
                    | sP0(X3,X2,X1,sK2) )
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
        & ( ~ r1_tsep_1(sK5,sK4)
          | ~ r1_tsep_1(sK5,sK3) ) )
      | sP1(sK4,sK5,sK3,sK2)
      | ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
        & ( ~ r1_tsep_1(sK4,sK5)
          | ~ r1_tsep_1(sK3,sK5) ) )
      | sP0(sK5,sK4,sK3,sK2) )
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f35,f34,f33,f32])).

fof(f61,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f42,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,(
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
    inference(equality_resolution,[],[f42])).

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

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X3,X2,X1,X0] :
      ( ( r1_tsep_1(X2,X3)
        & r1_tsep_1(X1,X3)
        & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tsep_1(X1,X0)
        & r1_tsep_1(X2,X0)
        & ~ r1_tsep_1(k1_tsep_1(X3,X2,X1),X0) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f30])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f28,plain,(
    ! [X2,X3,X1,X0] :
      ( ( r1_tsep_1(X3,X2)
        & r1_tsep_1(X3,X1)
        & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
      | ~ sP1(X2,X3,X1,X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tsep_1(X1,X0)
        & r1_tsep_1(X1,X2)
        & ~ r1_tsep_1(X1,k1_tsep_1(X3,X2,X0)) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,
    ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | sP1(sK4,sK5,sK3,sK2)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | sP0(sK5,sK4,sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X2,X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X1,k1_tsep_1(X3,X2,X0))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,
    ( ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3)
    | sP1(sK4,sK5,sK3,sK2)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | sP0(sK5,sK4,sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k1_tsep_1(X3,X2,X1),X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,
    ( ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3)
    | sP1(sK4,sK5,sK3,sK2)
    | ~ r1_tsep_1(sK4,sK5)
    | ~ r1_tsep_1(sK3,sK5)
    | sP0(sK5,sK4,sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X1,X2)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1043,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1646,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1043])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1041,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1648,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1041])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v1_pre_topc(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_177,plain,
    ( ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_11,c_10,c_9])).

cnf(c_178,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(renaming,[status(thm)],[c_177])).

cnf(c_1037,plain,
    ( ~ m1_pre_topc(X0_44,X1_44)
    | ~ m1_pre_topc(X2_44,X1_44)
    | v2_struct_0(X0_44)
    | v2_struct_0(X1_44)
    | v2_struct_0(X2_44)
    | ~ l1_pre_topc(X1_44)
    | u1_struct_0(k1_tsep_1(X1_44,X0_44,X2_44)) = k2_xboole_0(u1_struct_0(X0_44),u1_struct_0(X2_44)) ),
    inference(subtyping,[status(esa)],[c_178])).

cnf(c_1652,plain,
    ( u1_struct_0(k1_tsep_1(X0_44,X1_44,X2_44)) = k2_xboole_0(u1_struct_0(X1_44),u1_struct_0(X2_44))
    | m1_pre_topc(X1_44,X0_44) != iProver_top
    | m1_pre_topc(X2_44,X0_44) != iProver_top
    | v2_struct_0(X0_44) = iProver_top
    | v2_struct_0(X1_44) = iProver_top
    | v2_struct_0(X2_44) = iProver_top
    | l1_pre_topc(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1037])).

cnf(c_2294,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK3,X0_44)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_44))
    | m1_pre_topc(X0_44,sK2) != iProver_top
    | v2_struct_0(X0_44) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1648,c_1652])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_31,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_32,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_33,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5422,plain,
    ( v2_struct_0(X0_44) = iProver_top
    | m1_pre_topc(X0_44,sK2) != iProver_top
    | u1_struct_0(k1_tsep_1(sK2,sK3,X0_44)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_44)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2294,c_31,c_32,c_33])).

cnf(c_5423,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK3,X0_44)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_44))
    | m1_pre_topc(X0_44,sK2) != iProver_top
    | v2_struct_0(X0_44) = iProver_top ),
    inference(renaming,[status(thm)],[c_5422])).

cnf(c_5429,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1646,c_5423])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_35,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5570,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5429,c_35])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1055,plain,
    ( ~ r1_xboole_0(X0_45,X1_45)
    | ~ r1_xboole_0(X0_45,X2_45)
    | r1_xboole_0(X0_45,k2_xboole_0(X2_45,X1_45)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1634,plain,
    ( r1_xboole_0(X0_45,X1_45) != iProver_top
    | r1_xboole_0(X0_45,X2_45) != iProver_top
    | r1_xboole_0(X0_45,k2_xboole_0(X2_45,X1_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1055])).

cnf(c_5572,plain,
    ( r1_xboole_0(X0_45,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) = iProver_top
    | r1_xboole_0(X0_45,u1_struct_0(sK4)) != iProver_top
    | r1_xboole_0(X0_45,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5570,c_1634])).

cnf(c_7,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1051,plain,
    ( r1_tsep_1(X0_44,X1_44)
    | ~ r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(X1_44))
    | ~ l1_struct_0(X1_44)
    | ~ l1_struct_0(X0_44) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1638,plain,
    ( r1_tsep_1(X0_44,X1_44) = iProver_top
    | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(X1_44)) != iProver_top
    | l1_struct_0(X1_44) != iProver_top
    | l1_struct_0(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1051])).

cnf(c_6272,plain,
    ( r1_tsep_1(X0_44,k1_tsep_1(sK2,sK3,sK4)) = iProver_top
    | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK4)) != iProver_top
    | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK3)) != iProver_top
    | l1_struct_0(X0_44) != iProver_top
    | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5572,c_1638])).

cnf(c_6276,plain,
    ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) = iProver_top
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) != iProver_top
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6272])).

cnf(c_1067,plain,
    ( X0_44 != X1_44
    | X2_44 != X3_44
    | X4_44 != X5_44
    | k1_tsep_1(X0_44,X2_44,X4_44) = k1_tsep_1(X1_44,X3_44,X5_44) ),
    theory(equality)).

cnf(c_1071,plain,
    ( ~ r1_tsep_1(X0_44,X1_44)
    | r1_tsep_1(X2_44,X3_44)
    | X2_44 != X0_44
    | X3_44 != X1_44 ),
    theory(equality)).

cnf(c_3038,plain,
    ( ~ r1_tsep_1(X0_44,k1_tsep_1(X1_44,X2_44,X3_44))
    | r1_tsep_1(X4_44,k1_tsep_1(X5_44,X6_44,X7_44))
    | X4_44 != X0_44
    | X5_44 != X1_44
    | X6_44 != X2_44
    | X7_44 != X3_44 ),
    inference(resolution,[status(thm)],[c_1067,c_1071])).

cnf(c_12,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1046,plain,
    ( ~ r1_tsep_1(X0_44,X1_44)
    | r1_tsep_1(X1_44,X0_44)
    | ~ l1_struct_0(X1_44)
    | ~ l1_struct_0(X0_44) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | r1_tsep_1(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_13,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | r1_tsep_1(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_19,negated_conjecture,
    ( sP0(sK5,sK4,sK3,sK2)
    | sP1(sK4,sK5,sK3,sK2)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_499,plain,
    ( sP0(sK5,sK4,sK3,sK2)
    | r1_tsep_1(X0,X1)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | sK4 != X1
    | sK3 != X2
    | sK2 != X3
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_500,plain,
    ( sP0(sK5,sK4,sK3,sK2)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK4) ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_673,plain,
    ( r1_tsep_1(X0,X1)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK4)
    | sK4 != X0
    | sK3 != X2
    | sK2 != X3
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_500])).

cnf(c_674,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK4,sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK4) ),
    inference(unflattening,[status(thm)],[c_673])).

cnf(c_1030,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK4,sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK4) ),
    inference(subtyping,[status(esa)],[c_674])).

cnf(c_2322,plain,
    ( r1_tsep_1(sK4,sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK4)
    | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
    | ~ l1_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_1046,c_1030])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_81,plain,
    ( ~ l1_pre_topc(sK5)
    | l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1053,plain,
    ( ~ m1_pre_topc(X0_44,X1_44)
    | ~ l1_pre_topc(X1_44)
    | l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1759,plain,
    ( ~ m1_pre_topc(X0_44,sK2)
    | l1_pre_topc(X0_44)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_1761,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_1759])).

cnf(c_1636,plain,
    ( m1_pre_topc(X0_44,X1_44) != iProver_top
    | l1_pre_topc(X1_44) != iProver_top
    | l1_pre_topc(X0_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1053])).

cnf(c_1822,plain,
    ( l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1646,c_1636])).

cnf(c_1824,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1822])).

cnf(c_1054,plain,
    ( ~ l1_pre_topc(X0_44)
    | l1_struct_0(X0_44) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2092,plain,
    ( ~ l1_pre_topc(sK4)
    | l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1054])).

cnf(c_2238,plain,
    ( ~ r1_tsep_1(sK4,sK5)
    | r1_tsep_1(sK5,sK4)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_2524,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2322,c_29,c_23,c_81,c_1761,c_1824,c_2092,c_2238])).

cnf(c_2525,plain,
    ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK4)
    | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) ),
    inference(renaming,[status(thm)],[c_2524])).

cnf(c_2556,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK2,sK3,sK4))
    | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1054])).

cnf(c_2902,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK3,sK4),sK2)
    | l1_pre_topc(k1_tsep_1(sK2,sK3,sK4))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1759])).

cnf(c_1049,plain,
    ( ~ m1_pre_topc(X0_44,X1_44)
    | ~ m1_pre_topc(X2_44,X1_44)
    | m1_pre_topc(k1_tsep_1(X1_44,X0_44,X2_44),X1_44)
    | v2_struct_0(X0_44)
    | v2_struct_0(X1_44)
    | v2_struct_0(X2_44)
    | ~ l1_pre_topc(X1_44) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1855,plain,
    ( ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(X1_44,sK2)
    | m1_pre_topc(k1_tsep_1(sK2,X0_44,X1_44),sK2)
    | v2_struct_0(X0_44)
    | v2_struct_0(X1_44)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1049])).

cnf(c_3173,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK4),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1855])).

cnf(c_3359,plain,
    ( r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2525,c_30,c_29,c_28,c_27,c_26,c_25,c_2556,c_2902,c_3173])).

cnf(c_3360,plain,
    ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_3359])).

cnf(c_5618,plain,
    ( r1_tsep_1(X0_44,k1_tsep_1(X1_44,X2_44,X3_44))
    | r1_tsep_1(sK5,sK4)
    | X3_44 != sK4
    | X2_44 != sK3
    | X1_44 != sK2
    | X0_44 != sK5 ),
    inference(resolution,[status(thm)],[c_3038,c_3360])).

cnf(c_5678,plain,
    ( r1_tsep_1(k1_tsep_1(X0_44,X1_44,X2_44),X3_44)
    | r1_tsep_1(sK5,sK4)
    | ~ l1_struct_0(X3_44)
    | ~ l1_struct_0(k1_tsep_1(X0_44,X1_44,X2_44))
    | X2_44 != sK4
    | X1_44 != sK3
    | X0_44 != sK2
    | X3_44 != sK5 ),
    inference(resolution,[status(thm)],[c_5618,c_1046])).

cnf(c_3811,plain,
    ( r1_tsep_1(sK5,sK4)
    | ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1051])).

cnf(c_8,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1050,plain,
    ( ~ r1_tsep_1(X0_44,X1_44)
    | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(X1_44))
    | ~ l1_struct_0(X1_44)
    | ~ l1_struct_0(X0_44) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1639,plain,
    ( r1_tsep_1(X0_44,X1_44) != iProver_top
    | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(X1_44)) = iProver_top
    | l1_struct_0(X1_44) != iProver_top
    | l1_struct_0(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1050])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1057,plain,
    ( r1_xboole_0(X0_45,X1_45)
    | ~ r1_xboole_0(X0_45,k2_xboole_0(X2_45,X1_45)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1632,plain,
    ( r1_xboole_0(X0_45,X1_45) = iProver_top
    | r1_xboole_0(X0_45,k2_xboole_0(X2_45,X1_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1057])).

cnf(c_5573,plain,
    ( r1_xboole_0(X0_45,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) != iProver_top
    | r1_xboole_0(X0_45,u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5570,c_1632])).

cnf(c_5966,plain,
    ( r1_tsep_1(X0_44,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK4)) = iProver_top
    | l1_struct_0(X0_44) != iProver_top
    | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1639,c_5573])).

cnf(c_5967,plain,
    ( ~ r1_tsep_1(X0_44,k1_tsep_1(sK2,sK3,sK4))
    | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK4))
    | ~ l1_struct_0(X0_44)
    | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5966])).

cnf(c_5969,plain,
    ( ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
    | ~ l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_5967])).

cnf(c_5971,plain,
    ( r1_tsep_1(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5678,c_30,c_29,c_28,c_27,c_26,c_25,c_23,c_81,c_1761,c_1824,c_2092,c_2525,c_2556,c_2902,c_3173,c_3811,c_5969])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | r1_tsep_1(X2,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_15,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | ~ r1_tsep_1(X1,k1_tsep_1(X3,X2,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_21,negated_conjecture,
    ( sP0(sK5,sK4,sK3,sK2)
    | sP1(sK4,sK5,sK3,sK2)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_414,plain,
    ( sP0(sK5,sK4,sK3,sK2)
    | ~ r1_tsep_1(X0,k1_tsep_1(X1,X2,X3))
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3)
    | sK4 != X3
    | sK3 != X2
    | sK2 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_415,plain,
    ( sP0(sK5,sK4,sK3,sK2)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_652,plain,
    ( r1_tsep_1(X0,X1)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3)
    | sK4 != X2
    | sK3 != X0
    | sK2 != X3
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_415])).

cnf(c_653,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3) ),
    inference(unflattening,[status(thm)],[c_652])).

cnf(c_1031,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3) ),
    inference(subtyping,[status(esa)],[c_653])).

cnf(c_1867,plain,
    ( l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1648,c_1636])).

cnf(c_1868,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1867])).

cnf(c_1977,plain,
    ( r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK5,sK3)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_2095,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1054])).

cnf(c_3280,plain,
    ( r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK5,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1031,c_29,c_23,c_81,c_1761,c_1868,c_1977,c_2095])).

cnf(c_709,plain,
    ( r1_tsep_1(X0,X1)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3)
    | sK4 != X0
    | sK3 != X2
    | sK2 != X3
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_415])).

cnf(c_710,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK4,sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3) ),
    inference(unflattening,[status(thm)],[c_709])).

cnf(c_1028,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK4,sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3) ),
    inference(subtyping,[status(esa)],[c_710])).

cnf(c_1974,plain,
    ( r1_tsep_1(sK4,sK5)
    | ~ r1_tsep_1(sK5,sK4)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_3259,plain,
    ( ~ r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1028,c_29,c_23,c_81,c_1761,c_1824,c_1974,c_2092])).

cnf(c_3260,plain,
    ( r1_tsep_1(sK4,sK5)
    | ~ r1_tsep_1(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_3259])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_tsep_1(k1_tsep_1(X3,X2,X1),X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_22,negated_conjecture,
    ( sP0(sK5,sK4,sK3,sK2)
    | sP1(sK4,sK5,sK3,sK2)
    | ~ r1_tsep_1(sK4,sK5)
    | ~ r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_392,plain,
    ( sP0(sK5,sK4,sK3,sK2)
    | ~ r1_tsep_1(X0,k1_tsep_1(X1,X2,X3))
    | ~ r1_tsep_1(sK4,sK5)
    | ~ r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3)
    | sK4 != X3
    | sK3 != X2
    | sK2 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_393,plain,
    ( sP0(sK5,sK4,sK3,sK2)
    | ~ r1_tsep_1(sK4,sK5)
    | ~ r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_594,plain,
    ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
    | ~ r1_tsep_1(sK4,sK5)
    | ~ r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3)
    | sK4 != X2
    | sK3 != X1
    | sK2 != X0
    | sK5 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_393])).

cnf(c_595,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK4,sK5)
    | ~ r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3) ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_1034,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK4,sK5)
    | ~ r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3) ),
    inference(subtyping,[status(esa)],[c_595])).

cnf(c_3273,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3260,c_1034])).

cnf(c_3352,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3280,c_3273])).

cnf(c_2347,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
    | ~ l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_1655,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) != iProver_top
    | r1_tsep_1(sK4,sK5) != iProver_top
    | r1_tsep_1(sK3,sK5) != iProver_top
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | r1_tsep_1(sK5,sK4) != iProver_top
    | r1_tsep_1(sK5,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1034])).

cnf(c_38,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_80,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_82,plain,
    ( l1_pre_topc(sK5) != iProver_top
    | l1_struct_0(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(c_596,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) != iProver_top
    | r1_tsep_1(sK4,sK5) != iProver_top
    | r1_tsep_1(sK3,sK5) != iProver_top
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | r1_tsep_1(sK5,sK4) != iProver_top
    | r1_tsep_1(sK5,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_595])).

cnf(c_1760,plain,
    ( m1_pre_topc(X0_44,sK2) != iProver_top
    | l1_pre_topc(X0_44) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1759])).

cnf(c_1762,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1760])).

cnf(c_1975,plain,
    ( r1_tsep_1(sK4,sK5) = iProver_top
    | r1_tsep_1(sK5,sK4) != iProver_top
    | l1_struct_0(sK4) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1974])).

cnf(c_1978,plain,
    ( r1_tsep_1(sK3,sK5) = iProver_top
    | r1_tsep_1(sK5,sK3) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1977])).

cnf(c_2093,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2092])).

cnf(c_2096,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2095])).

cnf(c_2987,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) != iProver_top
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | r1_tsep_1(sK5,sK4) != iProver_top
    | r1_tsep_1(sK5,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1655,c_32,c_38,c_82,c_596,c_1762,c_1822,c_1867,c_1975,c_1978,c_2093,c_2096])).

cnf(c_2989,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2987])).

cnf(c_3619,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3352,c_30,c_29,c_28,c_27,c_26,c_25,c_23,c_81,c_1761,c_2347,c_2556,c_2902,c_2989,c_3173])).

cnf(c_5983,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5971,c_3619])).

cnf(c_3824,plain,
    ( r1_tsep_1(sK5,sK3)
    | ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1051])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1056,plain,
    ( r1_xboole_0(X0_45,X1_45)
    | ~ r1_xboole_0(X0_45,k2_xboole_0(X1_45,X2_45)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1633,plain,
    ( r1_xboole_0(X0_45,X1_45) = iProver_top
    | r1_xboole_0(X0_45,k2_xboole_0(X1_45,X2_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1056])).

cnf(c_5574,plain,
    ( r1_xboole_0(X0_45,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) != iProver_top
    | r1_xboole_0(X0_45,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5570,c_1633])).

cnf(c_6076,plain,
    ( r1_tsep_1(X0_44,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK3)) = iProver_top
    | l1_struct_0(X0_44) != iProver_top
    | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1639,c_5574])).

cnf(c_6077,plain,
    ( ~ r1_tsep_1(X0_44,k1_tsep_1(sK2,sK3,sK4))
    | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK3))
    | ~ l1_struct_0(X0_44)
    | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6076])).

cnf(c_6079,plain,
    ( ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
    | ~ l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_6077])).

cnf(c_6086,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5983,c_30,c_29,c_28,c_27,c_26,c_25,c_23,c_81,c_1761,c_1868,c_2095,c_2347,c_2556,c_2902,c_3173,c_3824,c_6079])).

cnf(c_6088,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6086])).

cnf(c_5973,plain,
    ( r1_tsep_1(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5971])).

cnf(c_4674,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
    | ~ l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_4680,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) = iProver_top
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4674])).

cnf(c_3174,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK4),sK2) = iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3173])).

cnf(c_14,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | r1_tsep_1(X1,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_460,plain,
    ( sP0(sK5,sK4,sK3,sK2)
    | r1_tsep_1(X0,X1)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | sK4 != X2
    | sK3 != X1
    | sK2 != X3
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_461,plain,
    ( sP0(sK5,sK4,sK3,sK2)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK3) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_691,plain,
    ( r1_tsep_1(X0,X1)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK3)
    | sK4 != X0
    | sK3 != X2
    | sK2 != X3
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_461])).

cnf(c_692,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK4,sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK3) ),
    inference(unflattening,[status(thm)],[c_691])).

cnf(c_1029,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK4,sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK3) ),
    inference(subtyping,[status(esa)],[c_692])).

cnf(c_2321,plain,
    ( r1_tsep_1(sK4,sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK3)
    | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
    | ~ l1_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_1046,c_1029])).

cnf(c_2249,plain,
    ( ~ r1_tsep_1(sK3,sK5)
    | r1_tsep_1(sK5,sK3)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_634,plain,
    ( r1_tsep_1(X0,X1)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK3)
    | sK4 != X2
    | sK3 != X0
    | sK2 != X3
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_461])).

cnf(c_635,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK3,sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK3) ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_1032,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK3,sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK3) ),
    inference(subtyping,[status(esa)],[c_635])).

cnf(c_2323,plain,
    ( r1_tsep_1(sK3,sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK3)
    | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
    | ~ l1_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_1046,c_1032])).

cnf(c_2448,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK3)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2321,c_29,c_23,c_81,c_1761,c_1868,c_2095,c_2249,c_2323])).

cnf(c_2449,plain,
    ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK3)
    | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) ),
    inference(renaming,[status(thm)],[c_2448])).

cnf(c_3154,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,sK3)
    | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
    | ~ l1_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_2449,c_1046])).

cnf(c_3155,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) = iProver_top
    | r1_tsep_1(sK5,sK3) = iProver_top
    | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3154])).

cnf(c_2903,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK4),sK2) != iProver_top
    | l1_pre_topc(k1_tsep_1(sK2,sK3,sK4)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2902])).

cnf(c_2557,plain,
    ( l1_pre_topc(k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2556])).

cnf(c_1983,plain,
    ( ~ r1_tsep_1(sK5,sK3)
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1050])).

cnf(c_1984,plain,
    ( r1_tsep_1(sK5,sK3) != iProver_top
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1983])).

cnf(c_1980,plain,
    ( ~ r1_tsep_1(sK5,sK4)
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1050])).

cnf(c_1981,plain,
    ( r1_tsep_1(sK5,sK4) != iProver_top
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) = iProver_top
    | l1_struct_0(sK4) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1980])).

cnf(c_36,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_34,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6276,c_6088,c_5973,c_4680,c_3174,c_3155,c_2903,c_2557,c_2096,c_2093,c_1984,c_1981,c_1867,c_1822,c_1762,c_82,c_38,c_36,c_35,c_34,c_33,c_32,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:31:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.02/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.01  
% 3.02/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.02/1.01  
% 3.02/1.01  ------  iProver source info
% 3.02/1.01  
% 3.02/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.02/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.02/1.01  git: non_committed_changes: false
% 3.02/1.01  git: last_make_outside_of_git: false
% 3.02/1.01  
% 3.02/1.01  ------ 
% 3.02/1.01  ------ Parsing...
% 3.02/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.02/1.01  
% 3.02/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.02/1.01  
% 3.02/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.02/1.01  
% 3.02/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.02/1.01  ------ Proving...
% 3.02/1.01  ------ Problem Properties 
% 3.02/1.01  
% 3.02/1.01  
% 3.02/1.01  clauses                                 30
% 3.02/1.01  conjectures                             8
% 3.02/1.01  EPR                                     11
% 3.02/1.01  Horn                                    17
% 3.02/1.01  unary                                   8
% 3.02/1.01  binary                                  3
% 3.02/1.01  lits                                    113
% 3.02/1.01  lits eq                                 3
% 3.02/1.01  fd_pure                                 0
% 3.02/1.01  fd_pseudo                               0
% 3.02/1.01  fd_cond                                 0
% 3.02/1.01  fd_pseudo_cond                          1
% 3.02/1.01  AC symbols                              0
% 3.02/1.01  
% 3.02/1.01  ------ Input Options Time Limit: Unbounded
% 3.02/1.01  
% 3.02/1.01  
% 3.02/1.01  ------ 
% 3.02/1.01  Current options:
% 3.02/1.01  ------ 
% 3.02/1.01  
% 3.02/1.01  
% 3.02/1.01  
% 3.02/1.01  
% 3.02/1.01  ------ Proving...
% 3.02/1.01  
% 3.02/1.01  
% 3.02/1.01  % SZS status Theorem for theBenchmark.p
% 3.02/1.01  
% 3.02/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.02/1.01  
% 3.02/1.01  fof(f8,conjecture,(
% 3.02/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~(r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & ~(r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & ~(r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1) & ~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & ~(r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & ~(r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))) & ~(r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3) & ~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)))))))),
% 3.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f9,negated_conjecture,(
% 3.02/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~(r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & ~(r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & ~(r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1) & ~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & ~(r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & ~(r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))) & ~(r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3) & ~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)))))))),
% 3.02/1.01    inference(negated_conjecture,[],[f8])).
% 3.02/1.01  
% 3.02/1.01  fof(f10,plain,(
% 3.02/1.01    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~(r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & ~(r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & ~(r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1) & ~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & ~(r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & ~(r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))) & ~(r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3) & ~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)))))))),
% 3.02/1.01    inference(pure_predicate_removal,[],[f9])).
% 3.02/1.01  
% 3.02/1.01  fof(f21,plain,(
% 3.02/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1))) | (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1) & ~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | (r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3))) | (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3) & ~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.02/1.01    inference(ennf_transformation,[],[f10])).
% 3.02/1.01  
% 3.02/1.01  fof(f22,plain,(
% 3.02/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1))) | (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1) & ~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | (r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3))) | (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3) & ~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.02/1.01    inference(flattening,[],[f21])).
% 3.02/1.01  
% 3.02/1.01  fof(f24,plain,(
% 3.02/1.01    ! [X2,X3,X1,X0] : ((r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1) & ~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | ~sP1(X2,X3,X1,X0))),
% 3.02/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.02/1.01  
% 3.02/1.01  fof(f23,plain,(
% 3.02/1.01    ! [X3,X2,X1,X0] : ((r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3) & ~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)) | ~sP0(X3,X2,X1,X0))),
% 3.02/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.02/1.01  
% 3.02/1.01  fof(f25,plain,(
% 3.02/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1))) | sP1(X2,X3,X1,X0) | (r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3))) | sP0(X3,X2,X1,X0)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.02/1.01    inference(definition_folding,[],[f22,f24,f23])).
% 3.02/1.01  
% 3.02/1.01  fof(f35,plain,(
% 3.02/1.01    ( ! [X2,X0,X1] : (? [X3] : (((r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1))) | sP1(X2,X3,X1,X0) | (r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3))) | sP0(X3,X2,X1,X0)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (((r1_tsep_1(sK5,k1_tsep_1(X0,X1,X2)) & (~r1_tsep_1(sK5,X2) | ~r1_tsep_1(sK5,X1))) | sP1(X2,sK5,X1,X0) | (r1_tsep_1(k1_tsep_1(X0,X1,X2),sK5) & (~r1_tsep_1(X2,sK5) | ~r1_tsep_1(X1,sK5))) | sP0(sK5,X2,X1,X0)) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 3.02/1.01    introduced(choice_axiom,[])).
% 3.02/1.01  
% 3.02/1.01  fof(f34,plain,(
% 3.02/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (((r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1))) | sP1(X2,X3,X1,X0) | (r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3))) | sP0(X3,X2,X1,X0)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (((r1_tsep_1(X3,k1_tsep_1(X0,X1,sK4)) & (~r1_tsep_1(X3,sK4) | ~r1_tsep_1(X3,X1))) | sP1(sK4,X3,X1,X0) | (r1_tsep_1(k1_tsep_1(X0,X1,sK4),X3) & (~r1_tsep_1(sK4,X3) | ~r1_tsep_1(X1,X3))) | sP0(X3,sK4,X1,X0)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.02/1.01    introduced(choice_axiom,[])).
% 3.02/1.01  
% 3.02/1.01  fof(f33,plain,(
% 3.02/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (((r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1))) | sP1(X2,X3,X1,X0) | (r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3))) | sP0(X3,X2,X1,X0)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (((r1_tsep_1(X3,k1_tsep_1(X0,sK3,X2)) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,sK3))) | sP1(X2,X3,sK3,X0) | (r1_tsep_1(k1_tsep_1(X0,sK3,X2),X3) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(sK3,X3))) | sP0(X3,X2,sK3,X0)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.02/1.01    introduced(choice_axiom,[])).
% 3.02/1.01  
% 3.02/1.01  fof(f32,plain,(
% 3.02/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1))) | sP1(X2,X3,X1,X0) | (r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3))) | sP0(X3,X2,X1,X0)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (((r1_tsep_1(X3,k1_tsep_1(sK2,X1,X2)) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1))) | sP1(X2,X3,X1,sK2) | (r1_tsep_1(k1_tsep_1(sK2,X1,X2),X3) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3))) | sP0(X3,X2,X1,sK2)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.02/1.01    introduced(choice_axiom,[])).
% 3.02/1.01  
% 3.02/1.01  fof(f36,plain,(
% 3.02/1.01    (((((r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) & (~r1_tsep_1(sK5,sK4) | ~r1_tsep_1(sK5,sK3))) | sP1(sK4,sK5,sK3,sK2) | (r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) & (~r1_tsep_1(sK4,sK5) | ~r1_tsep_1(sK3,sK5))) | sP0(sK5,sK4,sK3,sK2)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.02/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f35,f34,f33,f32])).
% 3.02/1.01  
% 3.02/1.01  fof(f61,plain,(
% 3.02/1.01    m1_pre_topc(sK4,sK2)),
% 3.02/1.01    inference(cnf_transformation,[],[f36])).
% 3.02/1.01  
% 3.02/1.01  fof(f59,plain,(
% 3.02/1.01    m1_pre_topc(sK3,sK2)),
% 3.02/1.01    inference(cnf_transformation,[],[f36])).
% 3.02/1.01  
% 3.02/1.01  fof(f4,axiom,(
% 3.02/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3))))))),
% 3.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f14,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.02/1.01    inference(ennf_transformation,[],[f4])).
% 3.02/1.01  
% 3.02/1.01  fof(f15,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/1.01    inference(flattening,[],[f14])).
% 3.02/1.01  
% 3.02/1.01  fof(f26,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3)) & (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/1.01    inference(nnf_transformation,[],[f15])).
% 3.02/1.01  
% 3.02/1.01  fof(f42,plain,(
% 3.02/1.01    ( ! [X2,X0,X3,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f26])).
% 3.02/1.01  
% 3.02/1.01  fof(f68,plain,(
% 3.02/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(equality_resolution,[],[f42])).
% 3.02/1.01  
% 3.02/1.01  fof(f6,axiom,(
% 3.02/1.01    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f17,plain,(
% 3.02/1.01    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.02/1.01    inference(ennf_transformation,[],[f6])).
% 3.02/1.01  
% 3.02/1.01  fof(f18,plain,(
% 3.02/1.01    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/1.01    inference(flattening,[],[f17])).
% 3.02/1.01  
% 3.02/1.01  fof(f46,plain,(
% 3.02/1.01    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f18])).
% 3.02/1.01  
% 3.02/1.01  fof(f47,plain,(
% 3.02/1.01    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f18])).
% 3.02/1.01  
% 3.02/1.01  fof(f48,plain,(
% 3.02/1.01    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f18])).
% 3.02/1.01  
% 3.02/1.01  fof(f56,plain,(
% 3.02/1.01    ~v2_struct_0(sK2)),
% 3.02/1.01    inference(cnf_transformation,[],[f36])).
% 3.02/1.01  
% 3.02/1.01  fof(f57,plain,(
% 3.02/1.01    l1_pre_topc(sK2)),
% 3.02/1.01    inference(cnf_transformation,[],[f36])).
% 3.02/1.01  
% 3.02/1.01  fof(f58,plain,(
% 3.02/1.01    ~v2_struct_0(sK3)),
% 3.02/1.01    inference(cnf_transformation,[],[f36])).
% 3.02/1.01  
% 3.02/1.01  fof(f60,plain,(
% 3.02/1.01    ~v2_struct_0(sK4)),
% 3.02/1.01    inference(cnf_transformation,[],[f36])).
% 3.02/1.01  
% 3.02/1.01  fof(f1,axiom,(
% 3.02/1.01    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f11,plain,(
% 3.02/1.01    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.02/1.01    inference(ennf_transformation,[],[f1])).
% 3.02/1.01  
% 3.02/1.01  fof(f37,plain,(
% 3.02/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.02/1.01    inference(cnf_transformation,[],[f11])).
% 3.02/1.01  
% 3.02/1.01  fof(f5,axiom,(
% 3.02/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 3.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f16,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.02/1.01    inference(ennf_transformation,[],[f5])).
% 3.02/1.01  
% 3.02/1.01  fof(f27,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.02/1.01    inference(nnf_transformation,[],[f16])).
% 3.02/1.01  
% 3.02/1.01  fof(f45,plain,(
% 3.02/1.01    ( ! [X0,X1] : (r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f27])).
% 3.02/1.01  
% 3.02/1.01  fof(f7,axiom,(
% 3.02/1.01    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 3.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f19,plain,(
% 3.02/1.01    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 3.02/1.01    inference(ennf_transformation,[],[f7])).
% 3.02/1.01  
% 3.02/1.01  fof(f20,plain,(
% 3.02/1.01    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 3.02/1.01    inference(flattening,[],[f19])).
% 3.02/1.01  
% 3.02/1.01  fof(f49,plain,(
% 3.02/1.01    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f20])).
% 3.02/1.01  
% 3.02/1.01  fof(f30,plain,(
% 3.02/1.01    ! [X3,X2,X1,X0] : ((r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3) & ~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)) | ~sP0(X3,X2,X1,X0))),
% 3.02/1.01    inference(nnf_transformation,[],[f23])).
% 3.02/1.01  
% 3.02/1.01  fof(f31,plain,(
% 3.02/1.01    ! [X0,X1,X2,X3] : ((r1_tsep_1(X1,X0) & r1_tsep_1(X2,X0) & ~r1_tsep_1(k1_tsep_1(X3,X2,X1),X0)) | ~sP0(X0,X1,X2,X3))),
% 3.02/1.01    inference(rectify,[],[f30])).
% 3.02/1.01  
% 3.02/1.01  fof(f55,plain,(
% 3.02/1.01    ( ! [X2,X0,X3,X1] : (r1_tsep_1(X1,X0) | ~sP0(X0,X1,X2,X3)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f31])).
% 3.02/1.01  
% 3.02/1.01  fof(f28,plain,(
% 3.02/1.01    ! [X2,X3,X1,X0] : ((r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1) & ~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | ~sP1(X2,X3,X1,X0))),
% 3.02/1.01    inference(nnf_transformation,[],[f24])).
% 3.02/1.01  
% 3.02/1.01  fof(f29,plain,(
% 3.02/1.01    ! [X0,X1,X2,X3] : ((r1_tsep_1(X1,X0) & r1_tsep_1(X1,X2) & ~r1_tsep_1(X1,k1_tsep_1(X3,X2,X0))) | ~sP1(X0,X1,X2,X3))),
% 3.02/1.01    inference(rectify,[],[f28])).
% 3.02/1.01  
% 3.02/1.01  fof(f52,plain,(
% 3.02/1.01    ( ! [X2,X0,X3,X1] : (r1_tsep_1(X1,X0) | ~sP1(X0,X1,X2,X3)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f29])).
% 3.02/1.01  
% 3.02/1.01  fof(f67,plain,(
% 3.02/1.01    r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) | sP1(sK4,sK5,sK3,sK2) | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) | sP0(sK5,sK4,sK3,sK2)),
% 3.02/1.01    inference(cnf_transformation,[],[f36])).
% 3.02/1.01  
% 3.02/1.01  fof(f63,plain,(
% 3.02/1.01    m1_pre_topc(sK5,sK2)),
% 3.02/1.01    inference(cnf_transformation,[],[f36])).
% 3.02/1.01  
% 3.02/1.01  fof(f2,axiom,(
% 3.02/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f12,plain,(
% 3.02/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.02/1.01    inference(ennf_transformation,[],[f2])).
% 3.02/1.01  
% 3.02/1.01  fof(f40,plain,(
% 3.02/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f12])).
% 3.02/1.01  
% 3.02/1.01  fof(f3,axiom,(
% 3.02/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f13,plain,(
% 3.02/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.02/1.01    inference(ennf_transformation,[],[f3])).
% 3.02/1.01  
% 3.02/1.01  fof(f41,plain,(
% 3.02/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f13])).
% 3.02/1.01  
% 3.02/1.01  fof(f44,plain,(
% 3.02/1.01    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f27])).
% 3.02/1.01  
% 3.02/1.01  fof(f39,plain,(
% 3.02/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f11])).
% 3.02/1.01  
% 3.02/1.01  fof(f54,plain,(
% 3.02/1.01    ( ! [X2,X0,X3,X1] : (r1_tsep_1(X2,X0) | ~sP0(X0,X1,X2,X3)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f31])).
% 3.02/1.01  
% 3.02/1.01  fof(f50,plain,(
% 3.02/1.01    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X1,k1_tsep_1(X3,X2,X0)) | ~sP1(X0,X1,X2,X3)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f29])).
% 3.02/1.01  
% 3.02/1.01  fof(f65,plain,(
% 3.02/1.01    ~r1_tsep_1(sK5,sK4) | ~r1_tsep_1(sK5,sK3) | sP1(sK4,sK5,sK3,sK2) | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) | sP0(sK5,sK4,sK3,sK2)),
% 3.02/1.01    inference(cnf_transformation,[],[f36])).
% 3.02/1.01  
% 3.02/1.01  fof(f53,plain,(
% 3.02/1.01    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(k1_tsep_1(X3,X2,X1),X0) | ~sP0(X0,X1,X2,X3)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f31])).
% 3.02/1.01  
% 3.02/1.01  fof(f64,plain,(
% 3.02/1.01    ~r1_tsep_1(sK5,sK4) | ~r1_tsep_1(sK5,sK3) | sP1(sK4,sK5,sK3,sK2) | ~r1_tsep_1(sK4,sK5) | ~r1_tsep_1(sK3,sK5) | sP0(sK5,sK4,sK3,sK2)),
% 3.02/1.01    inference(cnf_transformation,[],[f36])).
% 3.02/1.01  
% 3.02/1.01  fof(f38,plain,(
% 3.02/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f11])).
% 3.02/1.01  
% 3.02/1.01  fof(f51,plain,(
% 3.02/1.01    ( ! [X2,X0,X3,X1] : (r1_tsep_1(X1,X2) | ~sP1(X0,X1,X2,X3)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f29])).
% 3.02/1.01  
% 3.02/1.01  cnf(c_25,negated_conjecture,
% 3.02/1.01      ( m1_pre_topc(sK4,sK2) ),
% 3.02/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1043,negated_conjecture,
% 3.02/1.01      ( m1_pre_topc(sK4,sK2) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_25]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1646,plain,
% 3.02/1.01      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1043]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_27,negated_conjecture,
% 3.02/1.01      ( m1_pre_topc(sK3,sK2) ),
% 3.02/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1041,negated_conjecture,
% 3.02/1.01      ( m1_pre_topc(sK3,sK2) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_27]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1648,plain,
% 3.02/1.01      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1041]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_6,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.01      | ~ m1_pre_topc(X2,X1)
% 3.02/1.01      | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | v2_struct_0(X2)
% 3.02/1.01      | v2_struct_0(k1_tsep_1(X1,X0,X2))
% 3.02/1.01      | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 3.02/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_11,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.01      | ~ m1_pre_topc(X2,X1)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | v2_struct_0(X2)
% 3.02/1.01      | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
% 3.02/1.01      | ~ l1_pre_topc(X1) ),
% 3.02/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_10,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.01      | ~ m1_pre_topc(X2,X1)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | v2_struct_0(X2)
% 3.02/1.01      | v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 3.02/1.01      | ~ l1_pre_topc(X1) ),
% 3.02/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_9,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.01      | ~ m1_pre_topc(X2,X1)
% 3.02/1.01      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | v2_struct_0(X2)
% 3.02/1.01      | ~ l1_pre_topc(X1) ),
% 3.02/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_177,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X2,X1)
% 3.02/1.01      | ~ m1_pre_topc(X0,X1)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | v2_struct_0(X2)
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_6,c_11,c_10,c_9]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_178,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.01      | ~ m1_pre_topc(X2,X1)
% 3.02/1.01      | v2_struct_0(X0)
% 3.02/1.01      | v2_struct_0(X1)
% 3.02/1.01      | v2_struct_0(X2)
% 3.02/1.01      | ~ l1_pre_topc(X1)
% 3.02/1.01      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 3.02/1.01      inference(renaming,[status(thm)],[c_177]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1037,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0_44,X1_44)
% 3.02/1.01      | ~ m1_pre_topc(X2_44,X1_44)
% 3.02/1.01      | v2_struct_0(X0_44)
% 3.02/1.01      | v2_struct_0(X1_44)
% 3.02/1.01      | v2_struct_0(X2_44)
% 3.02/1.01      | ~ l1_pre_topc(X1_44)
% 3.02/1.01      | u1_struct_0(k1_tsep_1(X1_44,X0_44,X2_44)) = k2_xboole_0(u1_struct_0(X0_44),u1_struct_0(X2_44)) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_178]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1652,plain,
% 3.02/1.01      ( u1_struct_0(k1_tsep_1(X0_44,X1_44,X2_44)) = k2_xboole_0(u1_struct_0(X1_44),u1_struct_0(X2_44))
% 3.02/1.01      | m1_pre_topc(X1_44,X0_44) != iProver_top
% 3.02/1.01      | m1_pre_topc(X2_44,X0_44) != iProver_top
% 3.02/1.01      | v2_struct_0(X0_44) = iProver_top
% 3.02/1.01      | v2_struct_0(X1_44) = iProver_top
% 3.02/1.01      | v2_struct_0(X2_44) = iProver_top
% 3.02/1.01      | l1_pre_topc(X0_44) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1037]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2294,plain,
% 3.02/1.01      ( u1_struct_0(k1_tsep_1(sK2,sK3,X0_44)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_44))
% 3.02/1.01      | m1_pre_topc(X0_44,sK2) != iProver_top
% 3.02/1.01      | v2_struct_0(X0_44) = iProver_top
% 3.02/1.01      | v2_struct_0(sK3) = iProver_top
% 3.02/1.01      | v2_struct_0(sK2) = iProver_top
% 3.02/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_1648,c_1652]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_30,negated_conjecture,
% 3.02/1.01      ( ~ v2_struct_0(sK2) ),
% 3.02/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_31,plain,
% 3.02/1.01      ( v2_struct_0(sK2) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_29,negated_conjecture,
% 3.02/1.01      ( l1_pre_topc(sK2) ),
% 3.02/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_32,plain,
% 3.02/1.01      ( l1_pre_topc(sK2) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_28,negated_conjecture,
% 3.02/1.01      ( ~ v2_struct_0(sK3) ),
% 3.02/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_33,plain,
% 3.02/1.01      ( v2_struct_0(sK3) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5422,plain,
% 3.02/1.01      ( v2_struct_0(X0_44) = iProver_top
% 3.02/1.01      | m1_pre_topc(X0_44,sK2) != iProver_top
% 3.02/1.01      | u1_struct_0(k1_tsep_1(sK2,sK3,X0_44)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_44)) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_2294,c_31,c_32,c_33]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5423,plain,
% 3.02/1.01      ( u1_struct_0(k1_tsep_1(sK2,sK3,X0_44)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_44))
% 3.02/1.01      | m1_pre_topc(X0_44,sK2) != iProver_top
% 3.02/1.01      | v2_struct_0(X0_44) = iProver_top ),
% 3.02/1.01      inference(renaming,[status(thm)],[c_5422]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5429,plain,
% 3.02/1.01      ( u1_struct_0(k1_tsep_1(sK2,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))
% 3.02/1.01      | v2_struct_0(sK4) = iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_1646,c_5423]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_26,negated_conjecture,
% 3.02/1.01      ( ~ v2_struct_0(sK4) ),
% 3.02/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_35,plain,
% 3.02/1.01      ( v2_struct_0(sK4) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5570,plain,
% 3.02/1.01      ( u1_struct_0(k1_tsep_1(sK2,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_5429,c_35]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2,plain,
% 3.02/1.01      ( ~ r1_xboole_0(X0,X1)
% 3.02/1.01      | ~ r1_xboole_0(X0,X2)
% 3.02/1.01      | r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 3.02/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1055,plain,
% 3.02/1.01      ( ~ r1_xboole_0(X0_45,X1_45)
% 3.02/1.01      | ~ r1_xboole_0(X0_45,X2_45)
% 3.02/1.01      | r1_xboole_0(X0_45,k2_xboole_0(X2_45,X1_45)) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1634,plain,
% 3.02/1.01      ( r1_xboole_0(X0_45,X1_45) != iProver_top
% 3.02/1.01      | r1_xboole_0(X0_45,X2_45) != iProver_top
% 3.02/1.01      | r1_xboole_0(X0_45,k2_xboole_0(X2_45,X1_45)) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1055]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5572,plain,
% 3.02/1.01      ( r1_xboole_0(X0_45,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) = iProver_top
% 3.02/1.01      | r1_xboole_0(X0_45,u1_struct_0(sK4)) != iProver_top
% 3.02/1.01      | r1_xboole_0(X0_45,u1_struct_0(sK3)) != iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_5570,c_1634]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_7,plain,
% 3.02/1.01      ( r1_tsep_1(X0,X1)
% 3.02/1.01      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 3.02/1.01      | ~ l1_struct_0(X1)
% 3.02/1.01      | ~ l1_struct_0(X0) ),
% 3.02/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1051,plain,
% 3.02/1.01      ( r1_tsep_1(X0_44,X1_44)
% 3.02/1.01      | ~ r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(X1_44))
% 3.02/1.01      | ~ l1_struct_0(X1_44)
% 3.02/1.01      | ~ l1_struct_0(X0_44) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1638,plain,
% 3.02/1.01      ( r1_tsep_1(X0_44,X1_44) = iProver_top
% 3.02/1.01      | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(X1_44)) != iProver_top
% 3.02/1.01      | l1_struct_0(X1_44) != iProver_top
% 3.02/1.01      | l1_struct_0(X0_44) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1051]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_6272,plain,
% 3.02/1.01      ( r1_tsep_1(X0_44,k1_tsep_1(sK2,sK3,sK4)) = iProver_top
% 3.02/1.01      | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK4)) != iProver_top
% 3.02/1.01      | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK3)) != iProver_top
% 3.02/1.01      | l1_struct_0(X0_44) != iProver_top
% 3.02/1.01      | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_5572,c_1638]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_6276,plain,
% 3.02/1.01      ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) = iProver_top
% 3.02/1.01      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) != iProver_top
% 3.02/1.01      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.02/1.01      | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.02/1.01      | l1_struct_0(sK5) != iProver_top ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_6272]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1067,plain,
% 3.02/1.01      ( X0_44 != X1_44
% 3.02/1.01      | X2_44 != X3_44
% 3.02/1.01      | X4_44 != X5_44
% 3.02/1.01      | k1_tsep_1(X0_44,X2_44,X4_44) = k1_tsep_1(X1_44,X3_44,X5_44) ),
% 3.02/1.01      theory(equality) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1071,plain,
% 3.02/1.01      ( ~ r1_tsep_1(X0_44,X1_44)
% 3.02/1.01      | r1_tsep_1(X2_44,X3_44)
% 3.02/1.01      | X2_44 != X0_44
% 3.02/1.01      | X3_44 != X1_44 ),
% 3.02/1.01      theory(equality) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3038,plain,
% 3.02/1.01      ( ~ r1_tsep_1(X0_44,k1_tsep_1(X1_44,X2_44,X3_44))
% 3.02/1.01      | r1_tsep_1(X4_44,k1_tsep_1(X5_44,X6_44,X7_44))
% 3.02/1.01      | X4_44 != X0_44
% 3.02/1.01      | X5_44 != X1_44
% 3.02/1.01      | X6_44 != X2_44
% 3.02/1.01      | X7_44 != X3_44 ),
% 3.02/1.01      inference(resolution,[status(thm)],[c_1067,c_1071]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_12,plain,
% 3.02/1.01      ( ~ r1_tsep_1(X0,X1)
% 3.02/1.01      | r1_tsep_1(X1,X0)
% 3.02/1.01      | ~ l1_struct_0(X1)
% 3.02/1.01      | ~ l1_struct_0(X0) ),
% 3.02/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1046,plain,
% 3.02/1.01      ( ~ r1_tsep_1(X0_44,X1_44)
% 3.02/1.01      | r1_tsep_1(X1_44,X0_44)
% 3.02/1.01      | ~ l1_struct_0(X1_44)
% 3.02/1.01      | ~ l1_struct_0(X0_44) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_16,plain,
% 3.02/1.01      ( ~ sP0(X0,X1,X2,X3) | r1_tsep_1(X1,X0) ),
% 3.02/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_13,plain,
% 3.02/1.01      ( ~ sP1(X0,X1,X2,X3) | r1_tsep_1(X1,X0) ),
% 3.02/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_19,negated_conjecture,
% 3.02/1.01      ( sP0(sK5,sK4,sK3,sK2)
% 3.02/1.01      | sP1(sK4,sK5,sK3,sK2)
% 3.02/1.01      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) ),
% 3.02/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_499,plain,
% 3.02/1.01      ( sP0(sK5,sK4,sK3,sK2)
% 3.02/1.01      | r1_tsep_1(X0,X1)
% 3.02/1.01      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | sK4 != X1
% 3.02/1.01      | sK3 != X2
% 3.02/1.01      | sK2 != X3
% 3.02/1.01      | sK5 != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_500,plain,
% 3.02/1.01      ( sP0(sK5,sK4,sK3,sK2)
% 3.02/1.01      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_tsep_1(sK5,sK4) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_499]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_673,plain,
% 3.02/1.01      ( r1_tsep_1(X0,X1)
% 3.02/1.01      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_tsep_1(sK5,sK4)
% 3.02/1.01      | sK4 != X0
% 3.02/1.01      | sK3 != X2
% 3.02/1.01      | sK2 != X3
% 3.02/1.01      | sK5 != X1 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_500]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_674,plain,
% 3.02/1.01      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | r1_tsep_1(sK4,sK5)
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_tsep_1(sK5,sK4) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_673]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1030,plain,
% 3.02/1.01      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | r1_tsep_1(sK4,sK5)
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_tsep_1(sK5,sK4) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_674]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2322,plain,
% 3.02/1.01      ( r1_tsep_1(sK4,sK5)
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ l1_struct_0(sK5) ),
% 3.02/1.01      inference(resolution,[status(thm)],[c_1046,c_1030]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_23,negated_conjecture,
% 3.02/1.01      ( m1_pre_topc(sK5,sK2) ),
% 3.02/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3,plain,
% 3.02/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.02/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_81,plain,
% 3.02/1.01      ( ~ l1_pre_topc(sK5) | l1_struct_0(sK5) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.02/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1053,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0_44,X1_44)
% 3.02/1.01      | ~ l1_pre_topc(X1_44)
% 3.02/1.01      | l1_pre_topc(X0_44) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1759,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0_44,sK2)
% 3.02/1.01      | l1_pre_topc(X0_44)
% 3.02/1.01      | ~ l1_pre_topc(sK2) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_1053]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1761,plain,
% 3.02/1.01      ( ~ m1_pre_topc(sK5,sK2) | ~ l1_pre_topc(sK2) | l1_pre_topc(sK5) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_1759]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1636,plain,
% 3.02/1.01      ( m1_pre_topc(X0_44,X1_44) != iProver_top
% 3.02/1.01      | l1_pre_topc(X1_44) != iProver_top
% 3.02/1.01      | l1_pre_topc(X0_44) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1053]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1822,plain,
% 3.02/1.01      ( l1_pre_topc(sK4) = iProver_top
% 3.02/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_1646,c_1636]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1824,plain,
% 3.02/1.01      ( l1_pre_topc(sK4) | ~ l1_pre_topc(sK2) ),
% 3.02/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1822]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1054,plain,
% 3.02/1.01      ( ~ l1_pre_topc(X0_44) | l1_struct_0(X0_44) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2092,plain,
% 3.02/1.01      ( ~ l1_pre_topc(sK4) | l1_struct_0(sK4) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_1054]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2238,plain,
% 3.02/1.01      ( ~ r1_tsep_1(sK4,sK5)
% 3.02/1.01      | r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ l1_struct_0(sK4)
% 3.02/1.01      | ~ l1_struct_0(sK5) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_1046]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2524,plain,
% 3.02/1.01      ( ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_tsep_1(sK5,sK4)
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_2322,c_29,c_23,c_81,c_1761,c_1824,c_2092,c_2238]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2525,plain,
% 3.02/1.01      ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) ),
% 3.02/1.01      inference(renaming,[status(thm)],[c_2524]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2556,plain,
% 3.02/1.01      ( ~ l1_pre_topc(k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_1054]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2902,plain,
% 3.02/1.01      ( ~ m1_pre_topc(k1_tsep_1(sK2,sK3,sK4),sK2)
% 3.02/1.01      | l1_pre_topc(k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ l1_pre_topc(sK2) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_1759]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1049,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0_44,X1_44)
% 3.02/1.01      | ~ m1_pre_topc(X2_44,X1_44)
% 3.02/1.01      | m1_pre_topc(k1_tsep_1(X1_44,X0_44,X2_44),X1_44)
% 3.02/1.01      | v2_struct_0(X0_44)
% 3.02/1.01      | v2_struct_0(X1_44)
% 3.02/1.01      | v2_struct_0(X2_44)
% 3.02/1.01      | ~ l1_pre_topc(X1_44) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_9]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1855,plain,
% 3.02/1.01      ( ~ m1_pre_topc(X0_44,sK2)
% 3.02/1.01      | ~ m1_pre_topc(X1_44,sK2)
% 3.02/1.01      | m1_pre_topc(k1_tsep_1(sK2,X0_44,X1_44),sK2)
% 3.02/1.01      | v2_struct_0(X0_44)
% 3.02/1.01      | v2_struct_0(X1_44)
% 3.02/1.01      | v2_struct_0(sK2)
% 3.02/1.01      | ~ l1_pre_topc(sK2) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_1049]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3173,plain,
% 3.02/1.01      ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK4),sK2)
% 3.02/1.01      | ~ m1_pre_topc(sK4,sK2)
% 3.02/1.01      | ~ m1_pre_topc(sK3,sK2)
% 3.02/1.01      | v2_struct_0(sK4)
% 3.02/1.01      | v2_struct_0(sK3)
% 3.02/1.01      | v2_struct_0(sK2)
% 3.02/1.01      | ~ l1_pre_topc(sK2) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_1855]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3359,plain,
% 3.02/1.01      ( r1_tsep_1(sK5,sK4) | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_2525,c_30,c_29,c_28,c_27,c_26,c_25,c_2556,c_2902,
% 3.02/1.01                 c_3173]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3360,plain,
% 3.02/1.01      ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) | r1_tsep_1(sK5,sK4) ),
% 3.02/1.01      inference(renaming,[status(thm)],[c_3359]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5618,plain,
% 3.02/1.01      ( r1_tsep_1(X0_44,k1_tsep_1(X1_44,X2_44,X3_44))
% 3.02/1.01      | r1_tsep_1(sK5,sK4)
% 3.02/1.01      | X3_44 != sK4
% 3.02/1.01      | X2_44 != sK3
% 3.02/1.01      | X1_44 != sK2
% 3.02/1.01      | X0_44 != sK5 ),
% 3.02/1.01      inference(resolution,[status(thm)],[c_3038,c_3360]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5678,plain,
% 3.02/1.01      ( r1_tsep_1(k1_tsep_1(X0_44,X1_44,X2_44),X3_44)
% 3.02/1.01      | r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ l1_struct_0(X3_44)
% 3.02/1.01      | ~ l1_struct_0(k1_tsep_1(X0_44,X1_44,X2_44))
% 3.02/1.01      | X2_44 != sK4
% 3.02/1.01      | X1_44 != sK3
% 3.02/1.01      | X0_44 != sK2
% 3.02/1.01      | X3_44 != sK5 ),
% 3.02/1.01      inference(resolution,[status(thm)],[c_5618,c_1046]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3811,plain,
% 3.02/1.01      ( r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
% 3.02/1.01      | ~ l1_struct_0(sK4)
% 3.02/1.01      | ~ l1_struct_0(sK5) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_1051]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_8,plain,
% 3.02/1.01      ( ~ r1_tsep_1(X0,X1)
% 3.02/1.01      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 3.02/1.01      | ~ l1_struct_0(X1)
% 3.02/1.01      | ~ l1_struct_0(X0) ),
% 3.02/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1050,plain,
% 3.02/1.01      ( ~ r1_tsep_1(X0_44,X1_44)
% 3.02/1.01      | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(X1_44))
% 3.02/1.01      | ~ l1_struct_0(X1_44)
% 3.02/1.01      | ~ l1_struct_0(X0_44) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1639,plain,
% 3.02/1.01      ( r1_tsep_1(X0_44,X1_44) != iProver_top
% 3.02/1.01      | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(X1_44)) = iProver_top
% 3.02/1.01      | l1_struct_0(X1_44) != iProver_top
% 3.02/1.01      | l1_struct_0(X0_44) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1050]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_0,plain,
% 3.02/1.01      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 3.02/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1057,plain,
% 3.02/1.01      ( r1_xboole_0(X0_45,X1_45)
% 3.02/1.01      | ~ r1_xboole_0(X0_45,k2_xboole_0(X2_45,X1_45)) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1632,plain,
% 3.02/1.01      ( r1_xboole_0(X0_45,X1_45) = iProver_top
% 3.02/1.01      | r1_xboole_0(X0_45,k2_xboole_0(X2_45,X1_45)) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1057]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5573,plain,
% 3.02/1.01      ( r1_xboole_0(X0_45,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) != iProver_top
% 3.02/1.01      | r1_xboole_0(X0_45,u1_struct_0(sK4)) = iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_5570,c_1632]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5966,plain,
% 3.02/1.01      ( r1_tsep_1(X0_44,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.02/1.01      | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK4)) = iProver_top
% 3.02/1.01      | l1_struct_0(X0_44) != iProver_top
% 3.02/1.01      | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_1639,c_5573]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5967,plain,
% 3.02/1.01      ( ~ r1_tsep_1(X0_44,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK4))
% 3.02/1.01      | ~ l1_struct_0(X0_44)
% 3.02/1.01      | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) ),
% 3.02/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_5966]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5969,plain,
% 3.02/1.01      ( ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
% 3.02/1.01      | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ l1_struct_0(sK5) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_5967]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5971,plain,
% 3.02/1.01      ( r1_tsep_1(sK5,sK4) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_5678,c_30,c_29,c_28,c_27,c_26,c_25,c_23,c_81,c_1761,
% 3.02/1.01                 c_1824,c_2092,c_2525,c_2556,c_2902,c_3173,c_3811,c_5969]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_17,plain,
% 3.02/1.01      ( ~ sP0(X0,X1,X2,X3) | r1_tsep_1(X2,X0) ),
% 3.02/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_15,plain,
% 3.02/1.01      ( ~ sP1(X0,X1,X2,X3) | ~ r1_tsep_1(X1,k1_tsep_1(X3,X2,X0)) ),
% 3.02/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_21,negated_conjecture,
% 3.02/1.01      ( sP0(sK5,sK4,sK3,sK2)
% 3.02/1.01      | sP1(sK4,sK5,sK3,sK2)
% 3.02/1.01      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK3) ),
% 3.02/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_414,plain,
% 3.02/1.01      ( sP0(sK5,sK4,sK3,sK2)
% 3.02/1.01      | ~ r1_tsep_1(X0,k1_tsep_1(X1,X2,X3))
% 3.02/1.01      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK3)
% 3.02/1.01      | sK4 != X3
% 3.02/1.01      | sK3 != X2
% 3.02/1.01      | sK2 != X1
% 3.02/1.01      | sK5 != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_415,plain,
% 3.02/1.01      ( sP0(sK5,sK4,sK3,sK2)
% 3.02/1.01      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK3) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_414]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_652,plain,
% 3.02/1.01      ( r1_tsep_1(X0,X1)
% 3.02/1.01      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK3)
% 3.02/1.01      | sK4 != X2
% 3.02/1.01      | sK3 != X0
% 3.02/1.01      | sK2 != X3
% 3.02/1.01      | sK5 != X1 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_415]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_653,plain,
% 3.02/1.01      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | r1_tsep_1(sK3,sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK3) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_652]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1031,plain,
% 3.02/1.01      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | r1_tsep_1(sK3,sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK3) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_653]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1867,plain,
% 3.02/1.01      ( l1_pre_topc(sK3) = iProver_top
% 3.02/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_1648,c_1636]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1868,plain,
% 3.02/1.01      ( l1_pre_topc(sK3) | ~ l1_pre_topc(sK2) ),
% 3.02/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1867]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1977,plain,
% 3.02/1.01      ( r1_tsep_1(sK3,sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK3)
% 3.02/1.01      | ~ l1_struct_0(sK3)
% 3.02/1.01      | ~ l1_struct_0(sK5) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_1046]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2095,plain,
% 3.02/1.01      ( ~ l1_pre_topc(sK3) | l1_struct_0(sK3) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_1054]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3280,plain,
% 3.02/1.01      ( r1_tsep_1(sK3,sK5) | ~ r1_tsep_1(sK5,sK3) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_1031,c_29,c_23,c_81,c_1761,c_1868,c_1977,c_2095]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_709,plain,
% 3.02/1.01      ( r1_tsep_1(X0,X1)
% 3.02/1.01      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK3)
% 3.02/1.01      | sK4 != X0
% 3.02/1.01      | sK3 != X2
% 3.02/1.01      | sK2 != X3
% 3.02/1.01      | sK5 != X1 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_415]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_710,plain,
% 3.02/1.01      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | r1_tsep_1(sK4,sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK3) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_709]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1028,plain,
% 3.02/1.01      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | r1_tsep_1(sK4,sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK3) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_710]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1974,plain,
% 3.02/1.01      ( r1_tsep_1(sK4,sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ l1_struct_0(sK4)
% 3.02/1.01      | ~ l1_struct_0(sK5) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_1046]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3259,plain,
% 3.02/1.01      ( ~ r1_tsep_1(sK5,sK4) | r1_tsep_1(sK4,sK5) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_1028,c_29,c_23,c_81,c_1761,c_1824,c_1974,c_2092]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3260,plain,
% 3.02/1.01      ( r1_tsep_1(sK4,sK5) | ~ r1_tsep_1(sK5,sK4) ),
% 3.02/1.01      inference(renaming,[status(thm)],[c_3259]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_18,plain,
% 3.02/1.01      ( ~ sP0(X0,X1,X2,X3) | ~ r1_tsep_1(k1_tsep_1(X3,X2,X1),X0) ),
% 3.02/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_22,negated_conjecture,
% 3.02/1.01      ( sP0(sK5,sK4,sK3,sK2)
% 3.02/1.01      | sP1(sK4,sK5,sK3,sK2)
% 3.02/1.01      | ~ r1_tsep_1(sK4,sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK3,sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK3) ),
% 3.02/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_392,plain,
% 3.02/1.01      ( sP0(sK5,sK4,sK3,sK2)
% 3.02/1.01      | ~ r1_tsep_1(X0,k1_tsep_1(X1,X2,X3))
% 3.02/1.01      | ~ r1_tsep_1(sK4,sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK3,sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK3)
% 3.02/1.01      | sK4 != X3
% 3.02/1.01      | sK3 != X2
% 3.02/1.01      | sK2 != X1
% 3.02/1.01      | sK5 != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_393,plain,
% 3.02/1.01      ( sP0(sK5,sK4,sK3,sK2)
% 3.02/1.01      | ~ r1_tsep_1(sK4,sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK3,sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK3) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_392]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_594,plain,
% 3.02/1.01      ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
% 3.02/1.01      | ~ r1_tsep_1(sK4,sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK3,sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK3)
% 3.02/1.01      | sK4 != X2
% 3.02/1.01      | sK3 != X1
% 3.02/1.01      | sK2 != X0
% 3.02/1.01      | sK5 != X3 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_393]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_595,plain,
% 3.02/1.01      ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK4,sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK3,sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK3) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_594]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1034,plain,
% 3.02/1.01      ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK4,sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK3,sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK3) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_595]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3273,plain,
% 3.02/1.01      ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK3,sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK3) ),
% 3.02/1.01      inference(backward_subsumption_resolution,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_3260,c_1034]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3352,plain,
% 3.02/1.01      ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK3) ),
% 3.02/1.01      inference(backward_subsumption_resolution,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_3280,c_3273]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2347,plain,
% 3.02/1.01      ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ l1_struct_0(sK5) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_1046]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1655,plain,
% 3.02/1.01      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) != iProver_top
% 3.02/1.01      | r1_tsep_1(sK4,sK5) != iProver_top
% 3.02/1.01      | r1_tsep_1(sK3,sK5) != iProver_top
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.02/1.01      | r1_tsep_1(sK5,sK4) != iProver_top
% 3.02/1.01      | r1_tsep_1(sK5,sK3) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1034]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_38,plain,
% 3.02/1.01      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_80,plain,
% 3.02/1.01      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_82,plain,
% 3.02/1.01      ( l1_pre_topc(sK5) != iProver_top
% 3.02/1.01      | l1_struct_0(sK5) = iProver_top ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_80]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_596,plain,
% 3.02/1.01      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) != iProver_top
% 3.02/1.01      | r1_tsep_1(sK4,sK5) != iProver_top
% 3.02/1.01      | r1_tsep_1(sK3,sK5) != iProver_top
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.02/1.01      | r1_tsep_1(sK5,sK4) != iProver_top
% 3.02/1.01      | r1_tsep_1(sK5,sK3) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_595]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1760,plain,
% 3.02/1.01      ( m1_pre_topc(X0_44,sK2) != iProver_top
% 3.02/1.01      | l1_pre_topc(X0_44) = iProver_top
% 3.02/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1759]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1762,plain,
% 3.02/1.01      ( m1_pre_topc(sK5,sK2) != iProver_top
% 3.02/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.02/1.01      | l1_pre_topc(sK5) = iProver_top ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_1760]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1975,plain,
% 3.02/1.01      ( r1_tsep_1(sK4,sK5) = iProver_top
% 3.02/1.01      | r1_tsep_1(sK5,sK4) != iProver_top
% 3.02/1.01      | l1_struct_0(sK4) != iProver_top
% 3.02/1.01      | l1_struct_0(sK5) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1974]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1978,plain,
% 3.02/1.01      ( r1_tsep_1(sK3,sK5) = iProver_top
% 3.02/1.01      | r1_tsep_1(sK5,sK3) != iProver_top
% 3.02/1.01      | l1_struct_0(sK3) != iProver_top
% 3.02/1.01      | l1_struct_0(sK5) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1977]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2093,plain,
% 3.02/1.01      ( l1_pre_topc(sK4) != iProver_top
% 3.02/1.01      | l1_struct_0(sK4) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2092]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2096,plain,
% 3.02/1.01      ( l1_pre_topc(sK3) != iProver_top
% 3.02/1.01      | l1_struct_0(sK3) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2095]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2987,plain,
% 3.02/1.01      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) != iProver_top
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.02/1.01      | r1_tsep_1(sK5,sK4) != iProver_top
% 3.02/1.01      | r1_tsep_1(sK5,sK3) != iProver_top ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_1655,c_32,c_38,c_82,c_596,c_1762,c_1822,c_1867,c_1975,
% 3.02/1.01                 c_1978,c_2093,c_2096]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2989,plain,
% 3.02/1.01      ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK3) ),
% 3.02/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_2987]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3619,plain,
% 3.02/1.01      ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK4)
% 3.02/1.01      | ~ r1_tsep_1(sK5,sK3) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_3352,c_30,c_29,c_28,c_27,c_26,c_25,c_23,c_81,c_1761,
% 3.02/1.01                 c_2347,c_2556,c_2902,c_2989,c_3173]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5983,plain,
% 3.02/1.01      ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) | ~ r1_tsep_1(sK5,sK3) ),
% 3.02/1.01      inference(backward_subsumption_resolution,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_5971,c_3619]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3824,plain,
% 3.02/1.01      ( r1_tsep_1(sK5,sK3)
% 3.02/1.01      | ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
% 3.02/1.01      | ~ l1_struct_0(sK3)
% 3.02/1.01      | ~ l1_struct_0(sK5) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_1051]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1,plain,
% 3.02/1.01      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.02/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1056,plain,
% 3.02/1.01      ( r1_xboole_0(X0_45,X1_45)
% 3.02/1.01      | ~ r1_xboole_0(X0_45,k2_xboole_0(X1_45,X2_45)) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1633,plain,
% 3.02/1.01      ( r1_xboole_0(X0_45,X1_45) = iProver_top
% 3.02/1.01      | r1_xboole_0(X0_45,k2_xboole_0(X1_45,X2_45)) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1056]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5574,plain,
% 3.02/1.01      ( r1_xboole_0(X0_45,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) != iProver_top
% 3.02/1.01      | r1_xboole_0(X0_45,u1_struct_0(sK3)) = iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_5570,c_1633]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_6076,plain,
% 3.02/1.01      ( r1_tsep_1(X0_44,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.02/1.01      | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK3)) = iProver_top
% 3.02/1.01      | l1_struct_0(X0_44) != iProver_top
% 3.02/1.01      | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_1639,c_5574]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_6077,plain,
% 3.02/1.01      ( ~ r1_tsep_1(X0_44,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK3))
% 3.02/1.01      | ~ l1_struct_0(X0_44)
% 3.02/1.01      | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) ),
% 3.02/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_6076]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_6079,plain,
% 3.02/1.01      ( ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
% 3.02/1.01      | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ l1_struct_0(sK5) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_6077]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_6086,plain,
% 3.02/1.01      ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_5983,c_30,c_29,c_28,c_27,c_26,c_25,c_23,c_81,c_1761,
% 3.02/1.01                 c_1868,c_2095,c_2347,c_2556,c_2902,c_3173,c_3824,c_6079]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_6088,plain,
% 3.02/1.01      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_6086]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5973,plain,
% 3.02/1.01      ( r1_tsep_1(sK5,sK4) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_5971]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4674,plain,
% 3.02/1.01      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ l1_struct_0(sK5) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_1046]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4680,plain,
% 3.02/1.01      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) = iProver_top
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.02/1.01      | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.02/1.01      | l1_struct_0(sK5) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_4674]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3174,plain,
% 3.02/1.01      ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK4),sK2) = iProver_top
% 3.02/1.01      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.02/1.01      | m1_pre_topc(sK3,sK2) != iProver_top
% 3.02/1.01      | v2_struct_0(sK4) = iProver_top
% 3.02/1.01      | v2_struct_0(sK3) = iProver_top
% 3.02/1.01      | v2_struct_0(sK2) = iProver_top
% 3.02/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_3173]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_14,plain,
% 3.02/1.01      ( ~ sP1(X0,X1,X2,X3) | r1_tsep_1(X1,X2) ),
% 3.02/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_460,plain,
% 3.02/1.01      ( sP0(sK5,sK4,sK3,sK2)
% 3.02/1.01      | r1_tsep_1(X0,X1)
% 3.02/1.01      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | sK4 != X2
% 3.02/1.01      | sK3 != X1
% 3.02/1.01      | sK2 != X3
% 3.02/1.01      | sK5 != X0 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_461,plain,
% 3.02/1.01      ( sP0(sK5,sK4,sK3,sK2)
% 3.02/1.01      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_tsep_1(sK5,sK3) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_460]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_691,plain,
% 3.02/1.01      ( r1_tsep_1(X0,X1)
% 3.02/1.01      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_tsep_1(sK5,sK3)
% 3.02/1.01      | sK4 != X0
% 3.02/1.01      | sK3 != X2
% 3.02/1.01      | sK2 != X3
% 3.02/1.01      | sK5 != X1 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_461]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_692,plain,
% 3.02/1.01      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | r1_tsep_1(sK4,sK5)
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_tsep_1(sK5,sK3) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_691]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1029,plain,
% 3.02/1.01      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | r1_tsep_1(sK4,sK5)
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_tsep_1(sK5,sK3) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_692]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2321,plain,
% 3.02/1.01      ( r1_tsep_1(sK4,sK5)
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_tsep_1(sK5,sK3)
% 3.02/1.01      | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ l1_struct_0(sK5) ),
% 3.02/1.01      inference(resolution,[status(thm)],[c_1046,c_1029]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2249,plain,
% 3.02/1.01      ( ~ r1_tsep_1(sK3,sK5)
% 3.02/1.01      | r1_tsep_1(sK5,sK3)
% 3.02/1.01      | ~ l1_struct_0(sK3)
% 3.02/1.01      | ~ l1_struct_0(sK5) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_1046]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_634,plain,
% 3.02/1.01      ( r1_tsep_1(X0,X1)
% 3.02/1.01      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_tsep_1(sK5,sK3)
% 3.02/1.01      | sK4 != X2
% 3.02/1.01      | sK3 != X0
% 3.02/1.01      | sK2 != X3
% 3.02/1.01      | sK5 != X1 ),
% 3.02/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_461]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_635,plain,
% 3.02/1.01      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | r1_tsep_1(sK3,sK5)
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_tsep_1(sK5,sK3) ),
% 3.02/1.01      inference(unflattening,[status(thm)],[c_634]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1032,plain,
% 3.02/1.01      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | r1_tsep_1(sK3,sK5)
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_tsep_1(sK5,sK3) ),
% 3.02/1.01      inference(subtyping,[status(esa)],[c_635]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2323,plain,
% 3.02/1.01      ( r1_tsep_1(sK3,sK5)
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_tsep_1(sK5,sK3)
% 3.02/1.01      | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ l1_struct_0(sK5) ),
% 3.02/1.01      inference(resolution,[status(thm)],[c_1046,c_1032]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2448,plain,
% 3.02/1.01      ( ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_tsep_1(sK5,sK3)
% 3.02/1.01      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_2321,c_29,c_23,c_81,c_1761,c_1868,c_2095,c_2249,
% 3.02/1.01                 c_2323]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2449,plain,
% 3.02/1.01      ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | r1_tsep_1(sK5,sK3)
% 3.02/1.01      | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) ),
% 3.02/1.01      inference(renaming,[status(thm)],[c_2448]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3154,plain,
% 3.02/1.01      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.02/1.01      | r1_tsep_1(sK5,sK3)
% 3.02/1.01      | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
% 3.02/1.01      | ~ l1_struct_0(sK5) ),
% 3.02/1.01      inference(resolution,[status(thm)],[c_2449,c_1046]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3155,plain,
% 3.02/1.01      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) = iProver_top
% 3.02/1.01      | r1_tsep_1(sK5,sK3) = iProver_top
% 3.02/1.01      | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.02/1.01      | l1_struct_0(sK5) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_3154]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2903,plain,
% 3.02/1.01      ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK4),sK2) != iProver_top
% 3.02/1.01      | l1_pre_topc(k1_tsep_1(sK2,sK3,sK4)) = iProver_top
% 3.02/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2902]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2557,plain,
% 3.02/1.01      ( l1_pre_topc(k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.02/1.01      | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2556]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1983,plain,
% 3.02/1.01      ( ~ r1_tsep_1(sK5,sK3)
% 3.02/1.01      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
% 3.02/1.01      | ~ l1_struct_0(sK3)
% 3.02/1.01      | ~ l1_struct_0(sK5) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_1050]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1984,plain,
% 3.02/1.01      ( r1_tsep_1(sK5,sK3) != iProver_top
% 3.02/1.01      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
% 3.02/1.01      | l1_struct_0(sK3) != iProver_top
% 3.02/1.01      | l1_struct_0(sK5) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1983]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1980,plain,
% 3.02/1.01      ( ~ r1_tsep_1(sK5,sK4)
% 3.02/1.01      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
% 3.02/1.01      | ~ l1_struct_0(sK4)
% 3.02/1.01      | ~ l1_struct_0(sK5) ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_1050]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1981,plain,
% 3.02/1.01      ( r1_tsep_1(sK5,sK4) != iProver_top
% 3.02/1.01      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) = iProver_top
% 3.02/1.01      | l1_struct_0(sK4) != iProver_top
% 3.02/1.01      | l1_struct_0(sK5) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1980]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_36,plain,
% 3.02/1.01      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_34,plain,
% 3.02/1.01      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(contradiction,plain,
% 3.02/1.01      ( $false ),
% 3.02/1.01      inference(minisat,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_6276,c_6088,c_5973,c_4680,c_3174,c_3155,c_2903,c_2557,
% 3.02/1.01                 c_2096,c_2093,c_1984,c_1981,c_1867,c_1822,c_1762,c_82,
% 3.02/1.01                 c_38,c_36,c_35,c_34,c_33,c_32,c_31]) ).
% 3.02/1.01  
% 3.02/1.01  
% 3.02/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.02/1.01  
% 3.02/1.01  ------                               Statistics
% 3.02/1.01  
% 3.02/1.01  ------ Selected
% 3.02/1.01  
% 3.02/1.01  total_time:                             0.373
% 3.02/1.01  
%------------------------------------------------------------------------------
