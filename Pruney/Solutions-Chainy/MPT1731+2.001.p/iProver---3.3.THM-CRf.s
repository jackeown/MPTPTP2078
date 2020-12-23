%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:14 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  238 (3179 expanded)
%              Number of clauses        :  173 ( 776 expanded)
%              Number of leaves         :   18 (1092 expanded)
%              Depth                    :   22
%              Number of atoms          : 1108 (38274 expanded)
%              Number of equality atoms :  247 ( 623 expanded)
%              Maximal formula depth    :   16 (   5 average)
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
                 => ( ( ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) )
                     => r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                     => ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) ) )
                    & ( ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) )
                     => r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
                    & ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                     => ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
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
                   => ( ( ( r1_tsep_1(X3,X2)
                          & r1_tsep_1(X3,X1) )
                       => r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                      & ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                       => ( r1_tsep_1(X3,X2)
                          & r1_tsep_1(X3,X1) ) )
                      & ( ( r1_tsep_1(X2,X3)
                          & r1_tsep_1(X1,X3) )
                       => r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
                      & ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                       => ( r1_tsep_1(X2,X3)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
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
                   => ( ( ( r1_tsep_1(X3,X2)
                          & r1_tsep_1(X3,X1) )
                       => r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                      & ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                       => ( r1_tsep_1(X3,X2)
                          & r1_tsep_1(X3,X1) ) )
                      & ( ( r1_tsep_1(X2,X3)
                          & r1_tsep_1(X1,X3) )
                       => r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
                      & ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                       => ( r1_tsep_1(X2,X3)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1) )
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3) )
                    | ( ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) )
                      & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
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
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1) )
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3) )
                    | ( ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) )
                      & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
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
    ! [X2,X1,X0,X3] :
      ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
        & r1_tsep_1(X3,X2)
        & r1_tsep_1(X3,X1) )
      | ~ sP1(X2,X1,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f23,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
        & r1_tsep_1(X2,X3)
        & r1_tsep_1(X1,X3) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( sP1(X2,X1,X0,X3)
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | sP0(X3,X2,X1,X0)
                    | ( ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) )
                      & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
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
          ( ( sP1(X2,X1,X0,X3)
            | ( ( ~ r1_tsep_1(X3,X2)
                | ~ r1_tsep_1(X3,X1) )
              & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
            | sP0(X3,X2,X1,X0)
            | ( ( ~ r1_tsep_1(X2,X3)
                | ~ r1_tsep_1(X1,X3) )
              & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ( sP1(X2,X1,X0,sK5)
          | ( ( ~ r1_tsep_1(sK5,X2)
              | ~ r1_tsep_1(sK5,X1) )
            & r1_tsep_1(sK5,k1_tsep_1(X0,X1,X2)) )
          | sP0(sK5,X2,X1,X0)
          | ( ( ~ r1_tsep_1(X2,sK5)
              | ~ r1_tsep_1(X1,sK5) )
            & r1_tsep_1(k1_tsep_1(X0,X1,X2),sK5) ) )
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( sP1(X2,X1,X0,X3)
                | ( ( ~ r1_tsep_1(X3,X2)
                    | ~ r1_tsep_1(X3,X1) )
                  & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                | sP0(X3,X2,X1,X0)
                | ( ( ~ r1_tsep_1(X2,X3)
                    | ~ r1_tsep_1(X1,X3) )
                  & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ( sP1(sK4,X1,X0,X3)
              | ( ( ~ r1_tsep_1(X3,sK4)
                  | ~ r1_tsep_1(X3,X1) )
                & r1_tsep_1(X3,k1_tsep_1(X0,X1,sK4)) )
              | sP0(X3,sK4,X1,X0)
              | ( ( ~ r1_tsep_1(sK4,X3)
                  | ~ r1_tsep_1(X1,X3) )
                & r1_tsep_1(k1_tsep_1(X0,X1,sK4),X3) ) )
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
                  ( ( sP1(X2,X1,X0,X3)
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | sP0(X3,X2,X1,X0)
                    | ( ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) )
                      & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( sP1(X2,sK3,X0,X3)
                  | ( ( ~ r1_tsep_1(X3,X2)
                      | ~ r1_tsep_1(X3,sK3) )
                    & r1_tsep_1(X3,k1_tsep_1(X0,sK3,X2)) )
                  | sP0(X3,X2,sK3,X0)
                  | ( ( ~ r1_tsep_1(X2,X3)
                      | ~ r1_tsep_1(sK3,X3) )
                    & r1_tsep_1(k1_tsep_1(X0,sK3,X2),X3) ) )
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
                    ( ( sP1(X2,X1,X0,X3)
                      | ( ( ~ r1_tsep_1(X3,X2)
                          | ~ r1_tsep_1(X3,X1) )
                        & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                      | sP0(X3,X2,X1,X0)
                      | ( ( ~ r1_tsep_1(X2,X3)
                          | ~ r1_tsep_1(X1,X3) )
                        & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
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
                  ( ( sP1(X2,X1,sK2,X3)
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(sK2,X1,X2)) )
                    | sP0(X3,X2,X1,sK2)
                    | ( ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) )
                      & r1_tsep_1(k1_tsep_1(sK2,X1,X2),X3) ) )
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
    ( ( sP1(sK4,sK3,sK2,sK5)
      | ( ( ~ r1_tsep_1(sK5,sK4)
          | ~ r1_tsep_1(sK5,sK3) )
        & r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) )
      | sP0(sK5,sK4,sK3,sK2)
      | ( ( ~ r1_tsep_1(sK4,sK5)
          | ~ r1_tsep_1(sK3,sK5) )
        & r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) ) )
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

fof(f30,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
        & r1_tsep_1(X2,X3)
        & r1_tsep_1(X1,X3) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ~ r1_tsep_1(k1_tsep_1(X3,X2,X1),X0)
        & r1_tsep_1(X1,X0)
        & r1_tsep_1(X2,X0) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f30])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f28,plain,(
    ! [X2,X1,X0,X3] :
      ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
        & r1_tsep_1(X3,X2)
        & r1_tsep_1(X3,X1) )
      | ~ sP1(X2,X1,X0,X3) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ~ r1_tsep_1(X3,k1_tsep_1(X2,X1,X0))
        & r1_tsep_1(X3,X0)
        & r1_tsep_1(X3,X1) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X3,k1_tsep_1(X2,X1,X0))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,
    ( sP1(sK4,sK3,sK2,sK5)
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3)
    | sP0(sK5,sK4,sK3,sK2)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) ),
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

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X2,X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X3,X1)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f64,plain,
    ( sP1(sK4,sK3,sK2,sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | sP0(sK5,sK4,sK3,sK2)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X3,X0)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k1_tsep_1(X3,X2,X1),X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,
    ( sP1(sK4,sK3,sK2,sK5)
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK5,sK3)
    | sP0(sK5,sK4,sK3,sK2)
    | ~ r1_tsep_1(sK4,sK5)
    | ~ r1_tsep_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f36])).

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

cnf(c_2336,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK3,X0_44)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_44))
    | m1_pre_topc(X0_44,sK2) != iProver_top
    | v2_struct_0(X0_44) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
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

cnf(c_5391,plain,
    ( v2_struct_0(X0_44) = iProver_top
    | m1_pre_topc(X0_44,sK2) != iProver_top
    | u1_struct_0(k1_tsep_1(sK2,sK3,X0_44)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_44)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2336,c_31,c_32,c_33])).

cnf(c_5392,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK3,X0_44)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_44))
    | m1_pre_topc(X0_44,sK2) != iProver_top
    | v2_struct_0(X0_44) = iProver_top ),
    inference(renaming,[status(thm)],[c_5391])).

cnf(c_5398,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1646,c_5392])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1855,plain,
    ( ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(X1_44,sK2)
    | v2_struct_0(X0_44)
    | v2_struct_0(X1_44)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(k1_tsep_1(sK2,X0_44,X1_44)) = k2_xboole_0(u1_struct_0(X0_44),u1_struct_0(X1_44)) ),
    inference(instantiation,[status(thm)],[c_1037])).

cnf(c_4733,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(k1_tsep_1(sK2,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1855])).

cnf(c_5588,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5398,c_30,c_29,c_28,c_27,c_26,c_25,c_4733])).

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

cnf(c_5590,plain,
    ( r1_xboole_0(X0_45,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) = iProver_top
    | r1_xboole_0(X0_45,u1_struct_0(sK3)) != iProver_top
    | r1_xboole_0(X0_45,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5588,c_1634])).

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

cnf(c_6739,plain,
    ( r1_tsep_1(X0_44,k1_tsep_1(sK2,sK3,sK4)) = iProver_top
    | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK3)) != iProver_top
    | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK4)) != iProver_top
    | l1_struct_0(X0_44) != iProver_top
    | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5590,c_1638])).

cnf(c_6743,plain,
    ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) = iProver_top
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) != iProver_top
    | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6739])).

cnf(c_1061,plain,
    ( X0_44 != X1_44
    | X2_44 != X1_44
    | X2_44 = X0_44 ),
    theory(equality)).

cnf(c_1059,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_2460,plain,
    ( X0_44 != X1_44
    | X1_44 = X0_44 ),
    inference(resolution,[status(thm)],[c_1061,c_1059])).

cnf(c_1067,plain,
    ( X0_44 != X1_44
    | X2_44 != X3_44
    | X4_44 != X5_44
    | k1_tsep_1(X0_44,X2_44,X4_44) = k1_tsep_1(X1_44,X3_44,X5_44) ),
    theory(equality)).

cnf(c_3365,plain,
    ( X0_44 != X1_44
    | X2_44 != X3_44
    | X4_44 != X5_44
    | k1_tsep_1(X1_44,X3_44,X5_44) = k1_tsep_1(X0_44,X2_44,X4_44) ),
    inference(resolution,[status(thm)],[c_2460,c_1067])).

cnf(c_1071,plain,
    ( ~ r1_tsep_1(X0_44,X1_44)
    | r1_tsep_1(X2_44,X3_44)
    | X2_44 != X0_44
    | X3_44 != X1_44 ),
    theory(equality)).

cnf(c_2853,plain,
    ( ~ r1_tsep_1(X0_44,X1_44)
    | r1_tsep_1(X2_44,X1_44)
    | X2_44 != X0_44 ),
    inference(resolution,[status(thm)],[c_1071,c_1059])).

cnf(c_3764,plain,
    ( ~ r1_tsep_1(k1_tsep_1(X0_44,X1_44,X2_44),X3_44)
    | r1_tsep_1(k1_tsep_1(X4_44,X5_44,X6_44),X3_44)
    | X0_44 != X4_44
    | X1_44 != X5_44
    | X2_44 != X6_44 ),
    inference(resolution,[status(thm)],[c_3365,c_2853])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | r1_tsep_1(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_13,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | ~ r1_tsep_1(X3,k1_tsep_1(X2,X1,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_20,negated_conjecture,
    ( sP0(sK5,sK4,sK3,sK2)
    | sP1(sK4,sK3,sK2,sK5)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_474,plain,
    ( sP0(sK5,sK4,sK3,sK2)
    | ~ r1_tsep_1(X0,k1_tsep_1(X1,X2,X3))
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK5,sK4)
    | sK5 != X0
    | sK2 != X1
    | sK3 != X2
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_475,plain,
    ( sP0(sK5,sK4,sK3,sK2)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK5,sK4) ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_609,plain,
    ( r1_tsep_1(X0,X1)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK5,sK4)
    | sK5 != X1
    | sK2 != X2
    | sK3 != X3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_475])).

cnf(c_610,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_609])).

cnf(c_1033,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_610])).

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
    | l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1759])).

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

cnf(c_1980,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
    | ~ l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_1054,plain,
    ( ~ l1_pre_topc(X0_44)
    | l1_struct_0(X0_44) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2100,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK2,sK3,sK4))
    | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1054])).

cnf(c_2234,plain,
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

cnf(c_1850,plain,
    ( ~ m1_pre_topc(X0_44,sK2)
    | ~ m1_pre_topc(X1_44,sK2)
    | m1_pre_topc(k1_tsep_1(sK2,X0_44,X1_44),sK2)
    | v2_struct_0(X0_44)
    | v2_struct_0(X1_44)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1049])).

cnf(c_2310,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK4),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1850])).

cnf(c_2648,plain,
    ( ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1033,c_30,c_29,c_28,c_27,c_26,c_25,c_23,c_81,c_1761,c_1980,c_2100,c_2234,c_2310])).

cnf(c_2649,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) ),
    inference(renaming,[status(thm)],[c_2648])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | r1_tsep_1(X2,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_15,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | r1_tsep_1(X3,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_22,negated_conjecture,
    ( sP0(sK5,sK4,sK3,sK2)
    | sP1(sK4,sK3,sK2,sK5)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_392,plain,
    ( sP0(sK5,sK4,sK3,sK2)
    | r1_tsep_1(X0,X1)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | sK5 != X0
    | sK2 != X2
    | sK3 != X1
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_393,plain,
    ( sP0(sK5,sK4,sK3,sK2)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK3) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_591,plain,
    ( r1_tsep_1(X0,X1)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK3)
    | sK5 != X1
    | sK2 != X2
    | sK3 != X0
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_393])).

cnf(c_592,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK3)
    | r1_tsep_1(sK3,sK5) ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_1034,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK3)
    | r1_tsep_1(sK3,sK5) ),
    inference(subtyping,[status(esa)],[c_592])).

cnf(c_2666,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,sK3)
    | r1_tsep_1(sK3,sK5) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2649,c_1034])).

cnf(c_2117,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_1053,c_1041])).

cnf(c_1636,plain,
    ( m1_pre_topc(X0_44,X1_44) != iProver_top
    | l1_pre_topc(X1_44) != iProver_top
    | l1_pre_topc(X0_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1053])).

cnf(c_1862,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1648,c_1636])).

cnf(c_1863,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1862])).

cnf(c_2205,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2117,c_29,c_1863])).

cnf(c_2296,plain,
    ( l1_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_2205,c_1054])).

cnf(c_2688,plain,
    ( r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK3,sK5)
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_2726,plain,
    ( r1_tsep_1(sK5,sK3)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2666,c_29,c_23,c_81,c_1761,c_2296,c_2688])).

cnf(c_2727,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,sK3) ),
    inference(renaming,[status(thm)],[c_2726])).

cnf(c_5887,plain,
    ( r1_tsep_1(k1_tsep_1(X0_44,X1_44,X2_44),sK5)
    | r1_tsep_1(sK5,sK3)
    | sK2 != X0_44
    | sK3 != X1_44
    | sK4 != X2_44 ),
    inference(resolution,[status(thm)],[c_3764,c_2727])).

cnf(c_2744,plain,
    ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK3)
    | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
    | ~ l1_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_2727,c_1046])).

cnf(c_5106,plain,
    ( r1_tsep_1(sK5,sK3)
    | ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3) ),
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

cnf(c_5592,plain,
    ( r1_xboole_0(X0_45,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) != iProver_top
    | r1_xboole_0(X0_45,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5588,c_1633])).

cnf(c_6094,plain,
    ( r1_tsep_1(X0_44,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK3)) = iProver_top
    | l1_struct_0(X0_44) != iProver_top
    | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1639,c_5592])).

cnf(c_6095,plain,
    ( ~ r1_tsep_1(X0_44,k1_tsep_1(sK2,sK3,sK4))
    | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK3))
    | ~ l1_struct_0(X0_44)
    | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6094])).

cnf(c_6097,plain,
    ( ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
    | ~ l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_6095])).

cnf(c_6552,plain,
    ( r1_tsep_1(sK5,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5887,c_30,c_29,c_28,c_27,c_26,c_25,c_23,c_81,c_1761,c_2100,c_2234,c_2296,c_2310,c_2744,c_5106,c_6097])).

cnf(c_6554,plain,
    ( r1_tsep_1(sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6552])).

cnf(c_14,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | r1_tsep_1(X3,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_431,plain,
    ( sP0(sK5,sK4,sK3,sK2)
    | r1_tsep_1(X0,X1)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | sK5 != X0
    | sK2 != X2
    | sK3 != X3
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_432,plain,
    ( sP0(sK5,sK4,sK3,sK2)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK4) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_573,plain,
    ( r1_tsep_1(X0,X1)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK4)
    | sK5 != X1
    | sK2 != X2
    | sK3 != X0
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_432])).

cnf(c_574,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK3,sK5) ),
    inference(unflattening,[status(thm)],[c_573])).

cnf(c_1035,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK3,sK5) ),
    inference(subtyping,[status(esa)],[c_574])).

cnf(c_1654,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) = iProver_top
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) = iProver_top
    | r1_tsep_1(sK5,sK4) = iProver_top
    | r1_tsep_1(sK3,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1035])).

cnf(c_34,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_35,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_36,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

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

cnf(c_1760,plain,
    ( m1_pre_topc(X0_44,sK2) != iProver_top
    | l1_pre_topc(X0_44) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1759])).

cnf(c_1762,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | l1_pre_topc(sK5) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1760])).

cnf(c_2101,plain,
    ( l1_pre_topc(k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2100])).

cnf(c_2115,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK4) ),
    inference(resolution,[status(thm)],[c_1053,c_1043])).

cnf(c_1817,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1646,c_1636])).

cnf(c_1819,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1817])).

cnf(c_2190,plain,
    ( l1_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2115,c_29,c_1819])).

cnf(c_2202,plain,
    ( l1_struct_0(sK4) ),
    inference(resolution,[status(thm)],[c_2190,c_1054])).

cnf(c_2203,plain,
    ( l1_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2202])).

cnf(c_2235,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK4),sK2) != iProver_top
    | l1_pre_topc(k1_tsep_1(sK2,sK3,sK4)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2234])).

cnf(c_2311,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK4),sK2) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2310])).

cnf(c_630,plain,
    ( r1_tsep_1(X0,X1)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK4)
    | sK5 != X1
    | sK2 != X2
    | sK3 != X3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_432])).

cnf(c_631,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_630])).

cnf(c_1032,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_631])).

cnf(c_2364,plain,
    ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK4,sK5)
    | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
    | ~ l1_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_1046,c_1032])).

cnf(c_2369,plain,
    ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) = iProver_top
    | r1_tsep_1(sK5,sK4) = iProver_top
    | r1_tsep_1(sK4,sK5) = iProver_top
    | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2364])).

cnf(c_2629,plain,
    ( r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK4,sK5)
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_2635,plain,
    ( r1_tsep_1(sK5,sK4) = iProver_top
    | r1_tsep_1(sK4,sK5) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2629])).

cnf(c_2708,plain,
    ( r1_tsep_1(sK5,sK4) = iProver_top
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1654,c_31,c_32,c_33,c_34,c_35,c_36,c_38,c_82,c_1762,c_2101,c_2203,c_2235,c_2311,c_2369,c_2635])).

cnf(c_2709,plain,
    ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) = iProver_top
    | r1_tsep_1(sK5,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_2708])).

cnf(c_552,plain,
    ( r1_tsep_1(X0,X1)
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK5,sK4)
    | sK5 != X1
    | sK2 != X2
    | sK3 != X0
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_475])).

cnf(c_553,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK3,sK5) ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_1036,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK3,sK5) ),
    inference(subtyping,[status(esa)],[c_553])).

cnf(c_1653,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) = iProver_top
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | r1_tsep_1(sK5,sK3) != iProver_top
    | r1_tsep_1(sK5,sK4) != iProver_top
    | r1_tsep_1(sK3,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1036])).

cnf(c_1981,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) = iProver_top
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1980])).

cnf(c_2531,plain,
    ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1653,c_31,c_32,c_33,c_34,c_35,c_36,c_38,c_82,c_1762,c_1981,c_2101,c_2235,c_2311])).

cnf(c_2532,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) = iProver_top
    | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2531])).

cnf(c_2712,plain,
    ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) = iProver_top
    | r1_tsep_1(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2709,c_2532])).

cnf(c_5174,plain,
    ( r1_tsep_1(sK5,sK4)
    | ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1051])).

cnf(c_5175,plain,
    ( r1_tsep_1(sK5,sK4) = iProver_top
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5174])).

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

cnf(c_5591,plain,
    ( r1_xboole_0(X0_45,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) != iProver_top
    | r1_xboole_0(X0_45,u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5588,c_1632])).

cnf(c_5869,plain,
    ( r1_tsep_1(X0_44,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK4)) = iProver_top
    | l1_struct_0(X0_44) != iProver_top
    | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1639,c_5591])).

cnf(c_5871,plain,
    ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) = iProver_top
    | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5869])).

cnf(c_6317,plain,
    ( r1_tsep_1(sK5,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2712,c_31,c_32,c_33,c_34,c_35,c_36,c_38,c_82,c_1762,c_2101,c_2203,c_2235,c_2311,c_2709,c_5175,c_5871])).

cnf(c_3016,plain,
    ( ~ r1_tsep_1(sK5,sK4)
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1050])).

cnf(c_3025,plain,
    ( r1_tsep_1(sK5,sK4) != iProver_top
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) = iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3016])).

cnf(c_3017,plain,
    ( ~ r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK4,sK5)
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_3023,plain,
    ( r1_tsep_1(sK5,sK4) != iProver_top
    | r1_tsep_1(sK4,sK5) = iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3017])).

cnf(c_3005,plain,
    ( ~ r1_tsep_1(sK5,sK3)
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1050])).

cnf(c_3014,plain,
    ( r1_tsep_1(sK5,sK3) != iProver_top
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3005])).

cnf(c_3006,plain,
    ( ~ r1_tsep_1(sK5,sK3)
    | r1_tsep_1(sK3,sK5)
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_3012,plain,
    ( r1_tsep_1(sK5,sK3) != iProver_top
    | r1_tsep_1(sK3,sK5) = iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3006])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_tsep_1(k1_tsep_1(X3,X2,X1),X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_19,negated_conjecture,
    ( sP0(sK5,sK4,sK3,sK2)
    | sP1(sK4,sK3,sK2,sK5)
    | ~ r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_493,plain,
    ( sP0(sK5,sK4,sK3,sK2)
    | ~ r1_tsep_1(X0,k1_tsep_1(X1,X2,X3))
    | ~ r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK4,sK5)
    | sK5 != X0
    | sK2 != X1
    | sK3 != X2
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_494,plain,
    ( sP0(sK5,sK4,sK3,sK2)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_664,plain,
    ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK4,sK5)
    | sK5 != X3
    | sK2 != X0
    | sK3 != X1
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_494])).

cnf(c_665,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_1030,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
    | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_665])).

cnf(c_2662,plain,
    ( ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
    | ~ r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK5,sK4)
    | ~ r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK4,sK5) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2649,c_1030])).

cnf(c_2667,plain,
    ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | r1_tsep_1(sK5,sK3) != iProver_top
    | r1_tsep_1(sK5,sK4) != iProver_top
    | r1_tsep_1(sK3,sK5) != iProver_top
    | r1_tsep_1(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2662])).

cnf(c_2297,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2296])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6743,c_6554,c_6317,c_3025,c_3023,c_3014,c_3012,c_2667,c_2311,c_2297,c_2235,c_2203,c_2101,c_1762,c_82,c_38,c_36,c_35,c_34,c_33,c_32,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:42:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.59/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/0.98  
% 3.59/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.59/0.98  
% 3.59/0.98  ------  iProver source info
% 3.59/0.98  
% 3.59/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.59/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.59/0.98  git: non_committed_changes: false
% 3.59/0.98  git: last_make_outside_of_git: false
% 3.59/0.98  
% 3.59/0.98  ------ 
% 3.59/0.98  ------ Parsing...
% 3.59/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.59/0.98  ------ Proving...
% 3.59/0.98  ------ Problem Properties 
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  clauses                                 30
% 3.59/0.98  conjectures                             8
% 3.59/0.98  EPR                                     11
% 3.59/0.98  Horn                                    17
% 3.59/0.98  unary                                   8
% 3.59/0.98  binary                                  3
% 3.59/0.98  lits                                    113
% 3.59/0.98  lits eq                                 3
% 3.59/0.98  fd_pure                                 0
% 3.59/0.98  fd_pseudo                               0
% 3.59/0.98  fd_cond                                 0
% 3.59/0.98  fd_pseudo_cond                          1
% 3.59/0.98  AC symbols                              0
% 3.59/0.98  
% 3.59/0.98  ------ Input Options Time Limit: Unbounded
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  ------ 
% 3.59/0.98  Current options:
% 3.59/0.98  ------ 
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  ------ Proving...
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  % SZS status Theorem for theBenchmark.p
% 3.59/0.98  
% 3.59/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.59/0.98  
% 3.59/0.98  fof(f8,conjecture,(
% 3.59/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (((r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1)) => r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & (r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) => (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & ((r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3)) => r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)) & (r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) => (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))))))))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f9,negated_conjecture,(
% 3.59/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (((r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1)) => r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & (r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) => (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & ((r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3)) => r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)) & (r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) => (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))))))))),
% 3.59/0.98    inference(negated_conjecture,[],[f8])).
% 3.59/0.98  
% 3.59/0.98  fof(f10,plain,(
% 3.59/0.98    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (((r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1)) => r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & (r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) => (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & ((r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3)) => r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)) & (r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) => (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))))))))),
% 3.59/0.98    inference(pure_predicate_removal,[],[f9])).
% 3.59/0.98  
% 3.59/0.98  fof(f21,plain,(
% 3.59/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1)) & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | (~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))) | ((~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3)) & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.59/0.98    inference(ennf_transformation,[],[f10])).
% 3.59/0.98  
% 3.59/0.98  fof(f22,plain,(
% 3.59/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1)) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1)) & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | (~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3)) | ((~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3)) & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.59/0.98    inference(flattening,[],[f21])).
% 3.59/0.98  
% 3.59/0.98  fof(f24,plain,(
% 3.59/0.98    ! [X2,X1,X0,X3] : ((~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1)) | ~sP1(X2,X1,X0,X3))),
% 3.59/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.59/0.98  
% 3.59/0.98  fof(f23,plain,(
% 3.59/0.98    ! [X3,X2,X1,X0] : ((~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3)) | ~sP0(X3,X2,X1,X0))),
% 3.59/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.59/0.98  
% 3.59/0.98  fof(f25,plain,(
% 3.59/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((sP1(X2,X1,X0,X3) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1)) & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | sP0(X3,X2,X1,X0) | ((~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3)) & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.59/0.98    inference(definition_folding,[],[f22,f24,f23])).
% 3.59/0.98  
% 3.59/0.98  fof(f35,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (? [X3] : ((sP1(X2,X1,X0,X3) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1)) & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | sP0(X3,X2,X1,X0) | ((~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3)) & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((sP1(X2,X1,X0,sK5) | ((~r1_tsep_1(sK5,X2) | ~r1_tsep_1(sK5,X1)) & r1_tsep_1(sK5,k1_tsep_1(X0,X1,X2))) | sP0(sK5,X2,X1,X0) | ((~r1_tsep_1(X2,sK5) | ~r1_tsep_1(X1,sK5)) & r1_tsep_1(k1_tsep_1(X0,X1,X2),sK5))) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 3.59/0.98    introduced(choice_axiom,[])).
% 3.59/0.98  
% 3.59/0.98  fof(f34,plain,(
% 3.59/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : ((sP1(X2,X1,X0,X3) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1)) & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | sP0(X3,X2,X1,X0) | ((~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3)) & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : ((sP1(sK4,X1,X0,X3) | ((~r1_tsep_1(X3,sK4) | ~r1_tsep_1(X3,X1)) & r1_tsep_1(X3,k1_tsep_1(X0,X1,sK4))) | sP0(X3,sK4,X1,X0) | ((~r1_tsep_1(sK4,X3) | ~r1_tsep_1(X1,X3)) & r1_tsep_1(k1_tsep_1(X0,X1,sK4),X3))) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.59/0.98    introduced(choice_axiom,[])).
% 3.59/0.98  
% 3.59/0.98  fof(f33,plain,(
% 3.59/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((sP1(X2,X1,X0,X3) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1)) & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | sP0(X3,X2,X1,X0) | ((~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3)) & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((sP1(X2,sK3,X0,X3) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,sK3)) & r1_tsep_1(X3,k1_tsep_1(X0,sK3,X2))) | sP0(X3,X2,sK3,X0) | ((~r1_tsep_1(X2,X3) | ~r1_tsep_1(sK3,X3)) & r1_tsep_1(k1_tsep_1(X0,sK3,X2),X3))) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.59/0.98    introduced(choice_axiom,[])).
% 3.59/0.98  
% 3.59/0.98  fof(f32,plain,(
% 3.59/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((sP1(X2,X1,X0,X3) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1)) & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | sP0(X3,X2,X1,X0) | ((~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3)) & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((sP1(X2,X1,sK2,X3) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1)) & r1_tsep_1(X3,k1_tsep_1(sK2,X1,X2))) | sP0(X3,X2,X1,sK2) | ((~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3)) & r1_tsep_1(k1_tsep_1(sK2,X1,X2),X3))) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.59/0.98    introduced(choice_axiom,[])).
% 3.59/0.98  
% 3.59/0.98  fof(f36,plain,(
% 3.59/0.98    ((((sP1(sK4,sK3,sK2,sK5) | ((~r1_tsep_1(sK5,sK4) | ~r1_tsep_1(sK5,sK3)) & r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))) | sP0(sK5,sK4,sK3,sK2) | ((~r1_tsep_1(sK4,sK5) | ~r1_tsep_1(sK3,sK5)) & r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5))) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.59/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f35,f34,f33,f32])).
% 3.59/0.98  
% 3.59/0.98  fof(f61,plain,(
% 3.59/0.98    m1_pre_topc(sK4,sK2)),
% 3.59/0.98    inference(cnf_transformation,[],[f36])).
% 3.59/0.98  
% 3.59/0.98  fof(f59,plain,(
% 3.59/0.98    m1_pre_topc(sK3,sK2)),
% 3.59/0.98    inference(cnf_transformation,[],[f36])).
% 3.59/0.98  
% 3.59/0.98  fof(f4,axiom,(
% 3.59/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3))))))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f14,plain,(
% 3.59/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.59/0.98    inference(ennf_transformation,[],[f4])).
% 3.59/0.98  
% 3.59/0.98  fof(f15,plain,(
% 3.59/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.59/0.98    inference(flattening,[],[f14])).
% 3.59/0.98  
% 3.59/0.98  fof(f26,plain,(
% 3.59/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3)) & (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.59/0.98    inference(nnf_transformation,[],[f15])).
% 3.59/0.98  
% 3.59/0.98  fof(f42,plain,(
% 3.59/0.98    ( ! [X2,X0,X3,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f26])).
% 3.59/0.98  
% 3.59/0.98  fof(f68,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.59/0.98    inference(equality_resolution,[],[f42])).
% 3.59/0.98  
% 3.59/0.98  fof(f6,axiom,(
% 3.59/0.98    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f17,plain,(
% 3.59/0.98    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.59/0.98    inference(ennf_transformation,[],[f6])).
% 3.59/0.98  
% 3.59/0.98  fof(f18,plain,(
% 3.59/0.98    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.59/0.98    inference(flattening,[],[f17])).
% 3.59/0.98  
% 3.59/0.98  fof(f46,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f18])).
% 3.59/0.98  
% 3.59/0.98  fof(f47,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f18])).
% 3.59/0.98  
% 3.59/0.98  fof(f48,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f18])).
% 3.59/0.98  
% 3.59/0.98  fof(f56,plain,(
% 3.59/0.98    ~v2_struct_0(sK2)),
% 3.59/0.98    inference(cnf_transformation,[],[f36])).
% 3.59/0.98  
% 3.59/0.98  fof(f57,plain,(
% 3.59/0.98    l1_pre_topc(sK2)),
% 3.59/0.98    inference(cnf_transformation,[],[f36])).
% 3.59/0.98  
% 3.59/0.98  fof(f58,plain,(
% 3.59/0.98    ~v2_struct_0(sK3)),
% 3.59/0.98    inference(cnf_transformation,[],[f36])).
% 3.59/0.98  
% 3.59/0.98  fof(f60,plain,(
% 3.59/0.98    ~v2_struct_0(sK4)),
% 3.59/0.98    inference(cnf_transformation,[],[f36])).
% 3.59/0.98  
% 3.59/0.98  fof(f1,axiom,(
% 3.59/0.98    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f11,plain,(
% 3.59/0.98    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.59/0.98    inference(ennf_transformation,[],[f1])).
% 3.59/0.98  
% 3.59/0.98  fof(f37,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f11])).
% 3.59/0.98  
% 3.59/0.98  fof(f5,axiom,(
% 3.59/0.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f16,plain,(
% 3.59/0.98    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.59/0.98    inference(ennf_transformation,[],[f5])).
% 3.59/0.98  
% 3.59/0.98  fof(f27,plain,(
% 3.59/0.98    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.59/0.98    inference(nnf_transformation,[],[f16])).
% 3.59/0.98  
% 3.59/0.98  fof(f45,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f27])).
% 3.59/0.98  
% 3.59/0.98  fof(f30,plain,(
% 3.59/0.98    ! [X3,X2,X1,X0] : ((~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3)) | ~sP0(X3,X2,X1,X0))),
% 3.59/0.98    inference(nnf_transformation,[],[f23])).
% 3.59/0.98  
% 3.59/0.98  fof(f31,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3] : ((~r1_tsep_1(k1_tsep_1(X3,X2,X1),X0) & r1_tsep_1(X1,X0) & r1_tsep_1(X2,X0)) | ~sP0(X0,X1,X2,X3))),
% 3.59/0.98    inference(rectify,[],[f30])).
% 3.59/0.98  
% 3.59/0.98  fof(f54,plain,(
% 3.59/0.98    ( ! [X2,X0,X3,X1] : (r1_tsep_1(X1,X0) | ~sP0(X0,X1,X2,X3)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f31])).
% 3.59/0.98  
% 3.59/0.98  fof(f28,plain,(
% 3.59/0.98    ! [X2,X1,X0,X3] : ((~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1)) | ~sP1(X2,X1,X0,X3))),
% 3.59/0.98    inference(nnf_transformation,[],[f24])).
% 3.59/0.98  
% 3.59/0.98  fof(f29,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3] : ((~r1_tsep_1(X3,k1_tsep_1(X2,X1,X0)) & r1_tsep_1(X3,X0) & r1_tsep_1(X3,X1)) | ~sP1(X0,X1,X2,X3))),
% 3.59/0.98    inference(rectify,[],[f28])).
% 3.59/0.98  
% 3.59/0.98  fof(f52,plain,(
% 3.59/0.98    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X3,k1_tsep_1(X2,X1,X0)) | ~sP1(X0,X1,X2,X3)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f29])).
% 3.59/0.98  
% 3.59/0.98  fof(f66,plain,(
% 3.59/0.98    sP1(sK4,sK3,sK2,sK5) | ~r1_tsep_1(sK5,sK4) | ~r1_tsep_1(sK5,sK3) | sP0(sK5,sK4,sK3,sK2) | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)),
% 3.59/0.98    inference(cnf_transformation,[],[f36])).
% 3.59/0.98  
% 3.59/0.98  fof(f63,plain,(
% 3.59/0.98    m1_pre_topc(sK5,sK2)),
% 3.59/0.98    inference(cnf_transformation,[],[f36])).
% 3.59/0.98  
% 3.59/0.98  fof(f2,axiom,(
% 3.59/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f12,plain,(
% 3.59/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.59/0.98    inference(ennf_transformation,[],[f2])).
% 3.59/0.98  
% 3.59/0.98  fof(f40,plain,(
% 3.59/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f12])).
% 3.59/0.98  
% 3.59/0.98  fof(f3,axiom,(
% 3.59/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f13,plain,(
% 3.59/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.59/0.98    inference(ennf_transformation,[],[f3])).
% 3.59/0.98  
% 3.59/0.98  fof(f41,plain,(
% 3.59/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f13])).
% 3.59/0.98  
% 3.59/0.98  fof(f7,axiom,(
% 3.59/0.98    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f19,plain,(
% 3.59/0.98    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 3.59/0.98    inference(ennf_transformation,[],[f7])).
% 3.59/0.98  
% 3.59/0.98  fof(f20,plain,(
% 3.59/0.98    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 3.59/0.98    inference(flattening,[],[f19])).
% 3.59/0.98  
% 3.59/0.98  fof(f49,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f20])).
% 3.59/0.98  
% 3.59/0.98  fof(f53,plain,(
% 3.59/0.98    ( ! [X2,X0,X3,X1] : (r1_tsep_1(X2,X0) | ~sP0(X0,X1,X2,X3)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f31])).
% 3.59/0.98  
% 3.59/0.98  fof(f50,plain,(
% 3.59/0.98    ( ! [X2,X0,X3,X1] : (r1_tsep_1(X3,X1) | ~sP1(X0,X1,X2,X3)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f29])).
% 3.59/0.98  
% 3.59/0.98  fof(f64,plain,(
% 3.59/0.98    sP1(sK4,sK3,sK2,sK5) | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) | sP0(sK5,sK4,sK3,sK2) | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)),
% 3.59/0.98    inference(cnf_transformation,[],[f36])).
% 3.59/0.98  
% 3.59/0.98  fof(f44,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f27])).
% 3.59/0.98  
% 3.59/0.98  fof(f38,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f11])).
% 3.59/0.98  
% 3.59/0.98  fof(f51,plain,(
% 3.59/0.98    ( ! [X2,X0,X3,X1] : (r1_tsep_1(X3,X0) | ~sP1(X0,X1,X2,X3)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f29])).
% 3.59/0.98  
% 3.59/0.98  fof(f39,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f11])).
% 3.59/0.98  
% 3.59/0.98  fof(f55,plain,(
% 3.59/0.98    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(k1_tsep_1(X3,X2,X1),X0) | ~sP0(X0,X1,X2,X3)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f31])).
% 3.59/0.98  
% 3.59/0.98  fof(f67,plain,(
% 3.59/0.98    sP1(sK4,sK3,sK2,sK5) | ~r1_tsep_1(sK5,sK4) | ~r1_tsep_1(sK5,sK3) | sP0(sK5,sK4,sK3,sK2) | ~r1_tsep_1(sK4,sK5) | ~r1_tsep_1(sK3,sK5)),
% 3.59/0.98    inference(cnf_transformation,[],[f36])).
% 3.59/0.98  
% 3.59/0.98  cnf(c_25,negated_conjecture,
% 3.59/0.98      ( m1_pre_topc(sK4,sK2) ),
% 3.59/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1043,negated_conjecture,
% 3.59/0.98      ( m1_pre_topc(sK4,sK2) ),
% 3.59/0.98      inference(subtyping,[status(esa)],[c_25]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1646,plain,
% 3.59/0.98      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1043]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_27,negated_conjecture,
% 3.59/0.98      ( m1_pre_topc(sK3,sK2) ),
% 3.59/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1041,negated_conjecture,
% 3.59/0.98      ( m1_pre_topc(sK3,sK2) ),
% 3.59/0.98      inference(subtyping,[status(esa)],[c_27]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1648,plain,
% 3.59/0.98      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1041]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6,plain,
% 3.59/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.59/0.98      | ~ m1_pre_topc(X2,X1)
% 3.59/0.98      | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 3.59/0.98      | v2_struct_0(X1)
% 3.59/0.98      | v2_struct_0(X0)
% 3.59/0.98      | v2_struct_0(X2)
% 3.59/0.98      | v2_struct_0(k1_tsep_1(X1,X0,X2))
% 3.59/0.98      | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 3.59/0.98      | ~ l1_pre_topc(X1)
% 3.59/0.98      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 3.59/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_11,plain,
% 3.59/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.59/0.98      | ~ m1_pre_topc(X2,X1)
% 3.59/0.98      | v2_struct_0(X1)
% 3.59/0.98      | v2_struct_0(X0)
% 3.59/0.98      | v2_struct_0(X2)
% 3.59/0.98      | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
% 3.59/0.98      | ~ l1_pre_topc(X1) ),
% 3.59/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_10,plain,
% 3.59/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.59/0.98      | ~ m1_pre_topc(X2,X1)
% 3.59/0.98      | v2_struct_0(X1)
% 3.59/0.98      | v2_struct_0(X0)
% 3.59/0.98      | v2_struct_0(X2)
% 3.59/0.98      | v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 3.59/0.98      | ~ l1_pre_topc(X1) ),
% 3.59/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_9,plain,
% 3.59/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.59/0.98      | ~ m1_pre_topc(X2,X1)
% 3.59/0.98      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 3.59/0.98      | v2_struct_0(X1)
% 3.59/0.98      | v2_struct_0(X0)
% 3.59/0.98      | v2_struct_0(X2)
% 3.59/0.98      | ~ l1_pre_topc(X1) ),
% 3.59/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_177,plain,
% 3.59/0.98      ( ~ m1_pre_topc(X2,X1)
% 3.59/0.98      | ~ m1_pre_topc(X0,X1)
% 3.59/0.98      | v2_struct_0(X1)
% 3.59/0.98      | v2_struct_0(X0)
% 3.59/0.98      | v2_struct_0(X2)
% 3.59/0.98      | ~ l1_pre_topc(X1)
% 3.59/0.98      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_6,c_11,c_10,c_9]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_178,plain,
% 3.59/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.59/0.98      | ~ m1_pre_topc(X2,X1)
% 3.59/0.98      | v2_struct_0(X0)
% 3.59/0.98      | v2_struct_0(X1)
% 3.59/0.98      | v2_struct_0(X2)
% 3.59/0.98      | ~ l1_pre_topc(X1)
% 3.59/0.98      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 3.59/0.98      inference(renaming,[status(thm)],[c_177]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1037,plain,
% 3.59/0.98      ( ~ m1_pre_topc(X0_44,X1_44)
% 3.59/0.98      | ~ m1_pre_topc(X2_44,X1_44)
% 3.59/0.98      | v2_struct_0(X0_44)
% 3.59/0.98      | v2_struct_0(X1_44)
% 3.59/0.98      | v2_struct_0(X2_44)
% 3.59/0.98      | ~ l1_pre_topc(X1_44)
% 3.59/0.98      | u1_struct_0(k1_tsep_1(X1_44,X0_44,X2_44)) = k2_xboole_0(u1_struct_0(X0_44),u1_struct_0(X2_44)) ),
% 3.59/0.98      inference(subtyping,[status(esa)],[c_178]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1652,plain,
% 3.59/0.98      ( u1_struct_0(k1_tsep_1(X0_44,X1_44,X2_44)) = k2_xboole_0(u1_struct_0(X1_44),u1_struct_0(X2_44))
% 3.59/0.98      | m1_pre_topc(X1_44,X0_44) != iProver_top
% 3.59/0.98      | m1_pre_topc(X2_44,X0_44) != iProver_top
% 3.59/0.98      | v2_struct_0(X0_44) = iProver_top
% 3.59/0.98      | v2_struct_0(X1_44) = iProver_top
% 3.59/0.98      | v2_struct_0(X2_44) = iProver_top
% 3.59/0.98      | l1_pre_topc(X0_44) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1037]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2336,plain,
% 3.59/0.98      ( u1_struct_0(k1_tsep_1(sK2,sK3,X0_44)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_44))
% 3.59/0.98      | m1_pre_topc(X0_44,sK2) != iProver_top
% 3.59/0.98      | v2_struct_0(X0_44) = iProver_top
% 3.59/0.98      | v2_struct_0(sK2) = iProver_top
% 3.59/0.98      | v2_struct_0(sK3) = iProver_top
% 3.59/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1648,c_1652]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_30,negated_conjecture,
% 3.59/0.98      ( ~ v2_struct_0(sK2) ),
% 3.59/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_31,plain,
% 3.59/0.98      ( v2_struct_0(sK2) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_29,negated_conjecture,
% 3.59/0.98      ( l1_pre_topc(sK2) ),
% 3.59/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_32,plain,
% 3.59/0.98      ( l1_pre_topc(sK2) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_28,negated_conjecture,
% 3.59/0.98      ( ~ v2_struct_0(sK3) ),
% 3.59/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_33,plain,
% 3.59/0.98      ( v2_struct_0(sK3) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5391,plain,
% 3.59/0.98      ( v2_struct_0(X0_44) = iProver_top
% 3.59/0.98      | m1_pre_topc(X0_44,sK2) != iProver_top
% 3.59/0.98      | u1_struct_0(k1_tsep_1(sK2,sK3,X0_44)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_44)) ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_2336,c_31,c_32,c_33]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5392,plain,
% 3.59/0.98      ( u1_struct_0(k1_tsep_1(sK2,sK3,X0_44)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_44))
% 3.59/0.98      | m1_pre_topc(X0_44,sK2) != iProver_top
% 3.59/0.98      | v2_struct_0(X0_44) = iProver_top ),
% 3.59/0.98      inference(renaming,[status(thm)],[c_5391]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5398,plain,
% 3.59/0.98      ( u1_struct_0(k1_tsep_1(sK2,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))
% 3.59/0.98      | v2_struct_0(sK4) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1646,c_5392]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_26,negated_conjecture,
% 3.59/0.98      ( ~ v2_struct_0(sK4) ),
% 3.59/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1855,plain,
% 3.59/0.98      ( ~ m1_pre_topc(X0_44,sK2)
% 3.59/0.98      | ~ m1_pre_topc(X1_44,sK2)
% 3.59/0.98      | v2_struct_0(X0_44)
% 3.59/0.98      | v2_struct_0(X1_44)
% 3.59/0.98      | v2_struct_0(sK2)
% 3.59/0.98      | ~ l1_pre_topc(sK2)
% 3.59/0.98      | u1_struct_0(k1_tsep_1(sK2,X0_44,X1_44)) = k2_xboole_0(u1_struct_0(X0_44),u1_struct_0(X1_44)) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1037]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4733,plain,
% 3.59/0.98      ( ~ m1_pre_topc(sK3,sK2)
% 3.59/0.98      | ~ m1_pre_topc(sK4,sK2)
% 3.59/0.98      | v2_struct_0(sK2)
% 3.59/0.98      | v2_struct_0(sK3)
% 3.59/0.98      | v2_struct_0(sK4)
% 3.59/0.98      | ~ l1_pre_topc(sK2)
% 3.59/0.98      | u1_struct_0(k1_tsep_1(sK2,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1855]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5588,plain,
% 3.59/0.98      ( u1_struct_0(k1_tsep_1(sK2,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_5398,c_30,c_29,c_28,c_27,c_26,c_25,c_4733]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2,plain,
% 3.59/0.98      ( ~ r1_xboole_0(X0,X1)
% 3.59/0.98      | ~ r1_xboole_0(X0,X2)
% 3.59/0.98      | r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 3.59/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1055,plain,
% 3.59/0.98      ( ~ r1_xboole_0(X0_45,X1_45)
% 3.59/0.98      | ~ r1_xboole_0(X0_45,X2_45)
% 3.59/0.98      | r1_xboole_0(X0_45,k2_xboole_0(X2_45,X1_45)) ),
% 3.59/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1634,plain,
% 3.59/0.98      ( r1_xboole_0(X0_45,X1_45) != iProver_top
% 3.59/0.98      | r1_xboole_0(X0_45,X2_45) != iProver_top
% 3.59/0.98      | r1_xboole_0(X0_45,k2_xboole_0(X2_45,X1_45)) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1055]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5590,plain,
% 3.59/0.98      ( r1_xboole_0(X0_45,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) = iProver_top
% 3.59/0.98      | r1_xboole_0(X0_45,u1_struct_0(sK3)) != iProver_top
% 3.59/0.98      | r1_xboole_0(X0_45,u1_struct_0(sK4)) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_5588,c_1634]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_7,plain,
% 3.59/0.98      ( r1_tsep_1(X0,X1)
% 3.59/0.98      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 3.59/0.98      | ~ l1_struct_0(X1)
% 3.59/0.98      | ~ l1_struct_0(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1051,plain,
% 3.59/0.98      ( r1_tsep_1(X0_44,X1_44)
% 3.59/0.98      | ~ r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(X1_44))
% 3.59/0.98      | ~ l1_struct_0(X1_44)
% 3.59/0.98      | ~ l1_struct_0(X0_44) ),
% 3.59/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1638,plain,
% 3.59/0.98      ( r1_tsep_1(X0_44,X1_44) = iProver_top
% 3.59/0.98      | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(X1_44)) != iProver_top
% 3.59/0.98      | l1_struct_0(X1_44) != iProver_top
% 3.59/0.98      | l1_struct_0(X0_44) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1051]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6739,plain,
% 3.59/0.98      ( r1_tsep_1(X0_44,k1_tsep_1(sK2,sK3,sK4)) = iProver_top
% 3.59/0.98      | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK3)) != iProver_top
% 3.59/0.98      | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK4)) != iProver_top
% 3.59/0.98      | l1_struct_0(X0_44) != iProver_top
% 3.59/0.98      | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_5590,c_1638]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6743,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) = iProver_top
% 3.59/0.98      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.59/0.98      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) != iProver_top
% 3.59/0.98      | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.59/0.98      | l1_struct_0(sK5) != iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_6739]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1061,plain,
% 3.59/0.98      ( X0_44 != X1_44 | X2_44 != X1_44 | X2_44 = X0_44 ),
% 3.59/0.98      theory(equality) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1059,plain,( X0_44 = X0_44 ),theory(equality) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2460,plain,
% 3.59/0.98      ( X0_44 != X1_44 | X1_44 = X0_44 ),
% 3.59/0.98      inference(resolution,[status(thm)],[c_1061,c_1059]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1067,plain,
% 3.59/0.98      ( X0_44 != X1_44
% 3.59/0.98      | X2_44 != X3_44
% 3.59/0.98      | X4_44 != X5_44
% 3.59/0.98      | k1_tsep_1(X0_44,X2_44,X4_44) = k1_tsep_1(X1_44,X3_44,X5_44) ),
% 3.59/0.98      theory(equality) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3365,plain,
% 3.59/0.98      ( X0_44 != X1_44
% 3.59/0.98      | X2_44 != X3_44
% 3.59/0.98      | X4_44 != X5_44
% 3.59/0.98      | k1_tsep_1(X1_44,X3_44,X5_44) = k1_tsep_1(X0_44,X2_44,X4_44) ),
% 3.59/0.98      inference(resolution,[status(thm)],[c_2460,c_1067]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1071,plain,
% 3.59/0.98      ( ~ r1_tsep_1(X0_44,X1_44)
% 3.59/0.98      | r1_tsep_1(X2_44,X3_44)
% 3.59/0.98      | X2_44 != X0_44
% 3.59/0.98      | X3_44 != X1_44 ),
% 3.59/0.98      theory(equality) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2853,plain,
% 3.59/0.98      ( ~ r1_tsep_1(X0_44,X1_44)
% 3.59/0.98      | r1_tsep_1(X2_44,X1_44)
% 3.59/0.98      | X2_44 != X0_44 ),
% 3.59/0.98      inference(resolution,[status(thm)],[c_1071,c_1059]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3764,plain,
% 3.59/0.98      ( ~ r1_tsep_1(k1_tsep_1(X0_44,X1_44,X2_44),X3_44)
% 3.59/0.98      | r1_tsep_1(k1_tsep_1(X4_44,X5_44,X6_44),X3_44)
% 3.59/0.98      | X0_44 != X4_44
% 3.59/0.98      | X1_44 != X5_44
% 3.59/0.98      | X2_44 != X6_44 ),
% 3.59/0.98      inference(resolution,[status(thm)],[c_3365,c_2853]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_17,plain,
% 3.59/0.98      ( ~ sP0(X0,X1,X2,X3) | r1_tsep_1(X1,X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_13,plain,
% 3.59/0.98      ( ~ sP1(X0,X1,X2,X3) | ~ r1_tsep_1(X3,k1_tsep_1(X2,X1,X0)) ),
% 3.59/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_20,negated_conjecture,
% 3.59/0.98      ( sP0(sK5,sK4,sK3,sK2)
% 3.59/0.98      | sP1(sK4,sK3,sK2,sK5)
% 3.59/0.98      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK3)
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK4) ),
% 3.59/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_474,plain,
% 3.59/0.98      ( sP0(sK5,sK4,sK3,sK2)
% 3.59/0.98      | ~ r1_tsep_1(X0,k1_tsep_1(X1,X2,X3))
% 3.59/0.98      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK3)
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK4)
% 3.59/0.98      | sK5 != X0
% 3.59/0.98      | sK2 != X1
% 3.59/0.98      | sK3 != X2
% 3.59/0.98      | sK4 != X3 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_475,plain,
% 3.59/0.98      ( sP0(sK5,sK4,sK3,sK2)
% 3.59/0.98      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK3)
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK4) ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_474]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_609,plain,
% 3.59/0.98      ( r1_tsep_1(X0,X1)
% 3.59/0.98      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK3)
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK4)
% 3.59/0.98      | sK5 != X1
% 3.59/0.98      | sK2 != X2
% 3.59/0.98      | sK3 != X3
% 3.59/0.98      | sK4 != X0 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_475]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_610,plain,
% 3.59/0.98      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK3)
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK4)
% 3.59/0.98      | r1_tsep_1(sK4,sK5) ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_609]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1033,plain,
% 3.59/0.98      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK3)
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK4)
% 3.59/0.98      | r1_tsep_1(sK4,sK5) ),
% 3.59/0.98      inference(subtyping,[status(esa)],[c_610]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_23,negated_conjecture,
% 3.59/0.98      ( m1_pre_topc(sK5,sK2) ),
% 3.59/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3,plain,
% 3.59/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_81,plain,
% 3.59/0.98      ( ~ l1_pre_topc(sK5) | l1_struct_0(sK5) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4,plain,
% 3.59/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1053,plain,
% 3.59/0.98      ( ~ m1_pre_topc(X0_44,X1_44)
% 3.59/0.98      | ~ l1_pre_topc(X1_44)
% 3.59/0.98      | l1_pre_topc(X0_44) ),
% 3.59/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1759,plain,
% 3.59/0.98      ( ~ m1_pre_topc(X0_44,sK2)
% 3.59/0.98      | l1_pre_topc(X0_44)
% 3.59/0.98      | ~ l1_pre_topc(sK2) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1053]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1761,plain,
% 3.59/0.98      ( ~ m1_pre_topc(sK5,sK2) | l1_pre_topc(sK5) | ~ l1_pre_topc(sK2) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1759]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12,plain,
% 3.59/0.98      ( ~ r1_tsep_1(X0,X1)
% 3.59/0.98      | r1_tsep_1(X1,X0)
% 3.59/0.98      | ~ l1_struct_0(X1)
% 3.59/0.98      | ~ l1_struct_0(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1046,plain,
% 3.59/0.98      ( ~ r1_tsep_1(X0_44,X1_44)
% 3.59/0.98      | r1_tsep_1(X1_44,X0_44)
% 3.59/0.98      | ~ l1_struct_0(X1_44)
% 3.59/0.98      | ~ l1_struct_0(X0_44) ),
% 3.59/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1980,plain,
% 3.59/0.98      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | ~ l1_struct_0(sK5) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1046]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1054,plain,
% 3.59/0.98      ( ~ l1_pre_topc(X0_44) | l1_struct_0(X0_44) ),
% 3.59/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2100,plain,
% 3.59/0.98      ( ~ l1_pre_topc(k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1054]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2234,plain,
% 3.59/0.98      ( ~ m1_pre_topc(k1_tsep_1(sK2,sK3,sK4),sK2)
% 3.59/0.98      | l1_pre_topc(k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | ~ l1_pre_topc(sK2) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1759]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1049,plain,
% 3.59/0.98      ( ~ m1_pre_topc(X0_44,X1_44)
% 3.59/0.98      | ~ m1_pre_topc(X2_44,X1_44)
% 3.59/0.98      | m1_pre_topc(k1_tsep_1(X1_44,X0_44,X2_44),X1_44)
% 3.59/0.98      | v2_struct_0(X0_44)
% 3.59/0.98      | v2_struct_0(X1_44)
% 3.59/0.98      | v2_struct_0(X2_44)
% 3.59/0.98      | ~ l1_pre_topc(X1_44) ),
% 3.59/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1850,plain,
% 3.59/0.98      ( ~ m1_pre_topc(X0_44,sK2)
% 3.59/0.98      | ~ m1_pre_topc(X1_44,sK2)
% 3.59/0.98      | m1_pre_topc(k1_tsep_1(sK2,X0_44,X1_44),sK2)
% 3.59/0.98      | v2_struct_0(X0_44)
% 3.59/0.98      | v2_struct_0(X1_44)
% 3.59/0.98      | v2_struct_0(sK2)
% 3.59/0.98      | ~ l1_pre_topc(sK2) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1049]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2310,plain,
% 3.59/0.98      ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK4),sK2)
% 3.59/0.98      | ~ m1_pre_topc(sK3,sK2)
% 3.59/0.98      | ~ m1_pre_topc(sK4,sK2)
% 3.59/0.98      | v2_struct_0(sK2)
% 3.59/0.98      | v2_struct_0(sK3)
% 3.59/0.98      | v2_struct_0(sK4)
% 3.59/0.98      | ~ l1_pre_topc(sK2) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1850]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2648,plain,
% 3.59/0.98      ( ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_1033,c_30,c_29,c_28,c_27,c_26,c_25,c_23,c_81,c_1761,
% 3.59/0.98                 c_1980,c_2100,c_2234,c_2310]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2649,plain,
% 3.59/0.98      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) ),
% 3.59/0.98      inference(renaming,[status(thm)],[c_2648]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_18,plain,
% 3.59/0.98      ( ~ sP0(X0,X1,X2,X3) | r1_tsep_1(X2,X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_15,plain,
% 3.59/0.98      ( ~ sP1(X0,X1,X2,X3) | r1_tsep_1(X3,X1) ),
% 3.59/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_22,negated_conjecture,
% 3.59/0.98      ( sP0(sK5,sK4,sK3,sK2)
% 3.59/0.98      | sP1(sK4,sK3,sK2,sK5)
% 3.59/0.98      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) ),
% 3.59/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_392,plain,
% 3.59/0.98      ( sP0(sK5,sK4,sK3,sK2)
% 3.59/0.98      | r1_tsep_1(X0,X1)
% 3.59/0.98      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | sK5 != X0
% 3.59/0.98      | sK2 != X2
% 3.59/0.98      | sK3 != X1
% 3.59/0.98      | sK4 != X3 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_393,plain,
% 3.59/0.98      ( sP0(sK5,sK4,sK3,sK2)
% 3.59/0.98      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | r1_tsep_1(sK5,sK3) ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_392]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_591,plain,
% 3.59/0.98      ( r1_tsep_1(X0,X1)
% 3.59/0.98      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | r1_tsep_1(sK5,sK3)
% 3.59/0.98      | sK5 != X1
% 3.59/0.98      | sK2 != X2
% 3.59/0.98      | sK3 != X0
% 3.59/0.98      | sK4 != X3 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_393]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_592,plain,
% 3.59/0.98      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | r1_tsep_1(sK5,sK3)
% 3.59/0.98      | r1_tsep_1(sK3,sK5) ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_591]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1034,plain,
% 3.59/0.98      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | r1_tsep_1(sK5,sK3)
% 3.59/0.98      | r1_tsep_1(sK3,sK5) ),
% 3.59/0.98      inference(subtyping,[status(esa)],[c_592]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2666,plain,
% 3.59/0.98      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | r1_tsep_1(sK5,sK3)
% 3.59/0.98      | r1_tsep_1(sK3,sK5) ),
% 3.59/0.98      inference(backward_subsumption_resolution,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_2649,c_1034]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2117,plain,
% 3.59/0.98      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK3) ),
% 3.59/0.98      inference(resolution,[status(thm)],[c_1053,c_1041]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1636,plain,
% 3.59/0.98      ( m1_pre_topc(X0_44,X1_44) != iProver_top
% 3.59/0.98      | l1_pre_topc(X1_44) != iProver_top
% 3.59/0.98      | l1_pre_topc(X0_44) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1053]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1862,plain,
% 3.59/0.98      ( l1_pre_topc(sK2) != iProver_top
% 3.59/0.98      | l1_pre_topc(sK3) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1648,c_1636]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1863,plain,
% 3.59/0.98      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK3) ),
% 3.59/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1862]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2205,plain,
% 3.59/0.98      ( l1_pre_topc(sK3) ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_2117,c_29,c_1863]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2296,plain,
% 3.59/0.98      ( l1_struct_0(sK3) ),
% 3.59/0.98      inference(resolution,[status(thm)],[c_2205,c_1054]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2688,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,sK3)
% 3.59/0.98      | ~ r1_tsep_1(sK3,sK5)
% 3.59/0.98      | ~ l1_struct_0(sK5)
% 3.59/0.98      | ~ l1_struct_0(sK3) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1046]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2726,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,sK3) | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_2666,c_29,c_23,c_81,c_1761,c_2296,c_2688]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2727,plain,
% 3.59/0.98      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) | r1_tsep_1(sK5,sK3) ),
% 3.59/0.98      inference(renaming,[status(thm)],[c_2726]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5887,plain,
% 3.59/0.98      ( r1_tsep_1(k1_tsep_1(X0_44,X1_44,X2_44),sK5)
% 3.59/0.98      | r1_tsep_1(sK5,sK3)
% 3.59/0.98      | sK2 != X0_44
% 3.59/0.98      | sK3 != X1_44
% 3.59/0.98      | sK4 != X2_44 ),
% 3.59/0.98      inference(resolution,[status(thm)],[c_3764,c_2727]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2744,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | r1_tsep_1(sK5,sK3)
% 3.59/0.98      | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | ~ l1_struct_0(sK5) ),
% 3.59/0.98      inference(resolution,[status(thm)],[c_2727,c_1046]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5106,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,sK3)
% 3.59/0.98      | ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
% 3.59/0.98      | ~ l1_struct_0(sK5)
% 3.59/0.98      | ~ l1_struct_0(sK3) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1051]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_8,plain,
% 3.59/0.98      ( ~ r1_tsep_1(X0,X1)
% 3.59/0.98      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 3.59/0.98      | ~ l1_struct_0(X1)
% 3.59/0.98      | ~ l1_struct_0(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1050,plain,
% 3.59/0.98      ( ~ r1_tsep_1(X0_44,X1_44)
% 3.59/0.98      | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(X1_44))
% 3.59/0.98      | ~ l1_struct_0(X1_44)
% 3.59/0.98      | ~ l1_struct_0(X0_44) ),
% 3.59/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1639,plain,
% 3.59/0.98      ( r1_tsep_1(X0_44,X1_44) != iProver_top
% 3.59/0.98      | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(X1_44)) = iProver_top
% 3.59/0.98      | l1_struct_0(X1_44) != iProver_top
% 3.59/0.98      | l1_struct_0(X0_44) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1050]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1,plain,
% 3.59/0.98      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.59/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1056,plain,
% 3.59/0.98      ( r1_xboole_0(X0_45,X1_45)
% 3.59/0.98      | ~ r1_xboole_0(X0_45,k2_xboole_0(X1_45,X2_45)) ),
% 3.59/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1633,plain,
% 3.59/0.98      ( r1_xboole_0(X0_45,X1_45) = iProver_top
% 3.59/0.98      | r1_xboole_0(X0_45,k2_xboole_0(X1_45,X2_45)) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1056]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5592,plain,
% 3.59/0.98      ( r1_xboole_0(X0_45,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) != iProver_top
% 3.59/0.98      | r1_xboole_0(X0_45,u1_struct_0(sK3)) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_5588,c_1633]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6094,plain,
% 3.59/0.98      ( r1_tsep_1(X0_44,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.59/0.98      | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK3)) = iProver_top
% 3.59/0.98      | l1_struct_0(X0_44) != iProver_top
% 3.59/0.98      | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1639,c_5592]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6095,plain,
% 3.59/0.98      ( ~ r1_tsep_1(X0_44,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK3))
% 3.59/0.98      | ~ l1_struct_0(X0_44)
% 3.59/0.98      | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) ),
% 3.59/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_6094]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6097,plain,
% 3.59/0.98      ( ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
% 3.59/0.98      | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | ~ l1_struct_0(sK5) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_6095]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6552,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,sK3) ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_5887,c_30,c_29,c_28,c_27,c_26,c_25,c_23,c_81,c_1761,
% 3.59/0.98                 c_2100,c_2234,c_2296,c_2310,c_2744,c_5106,c_6097]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6554,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,sK3) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_6552]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_14,plain,
% 3.59/0.98      ( ~ sP1(X0,X1,X2,X3) | r1_tsep_1(X3,X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_431,plain,
% 3.59/0.98      ( sP0(sK5,sK4,sK3,sK2)
% 3.59/0.98      | r1_tsep_1(X0,X1)
% 3.59/0.98      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | sK5 != X0
% 3.59/0.98      | sK2 != X2
% 3.59/0.98      | sK3 != X3
% 3.59/0.98      | sK4 != X1 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_432,plain,
% 3.59/0.98      ( sP0(sK5,sK4,sK3,sK2)
% 3.59/0.98      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | r1_tsep_1(sK5,sK4) ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_431]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_573,plain,
% 3.59/0.98      ( r1_tsep_1(X0,X1)
% 3.59/0.98      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | r1_tsep_1(sK5,sK4)
% 3.59/0.98      | sK5 != X1
% 3.59/0.98      | sK2 != X2
% 3.59/0.98      | sK3 != X0
% 3.59/0.98      | sK4 != X3 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_432]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_574,plain,
% 3.59/0.98      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | r1_tsep_1(sK5,sK4)
% 3.59/0.98      | r1_tsep_1(sK3,sK5) ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_573]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1035,plain,
% 3.59/0.98      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | r1_tsep_1(sK5,sK4)
% 3.59/0.98      | r1_tsep_1(sK3,sK5) ),
% 3.59/0.98      inference(subtyping,[status(esa)],[c_574]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1654,plain,
% 3.59/0.98      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) = iProver_top
% 3.59/0.98      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) = iProver_top
% 3.59/0.98      | r1_tsep_1(sK5,sK4) = iProver_top
% 3.59/0.98      | r1_tsep_1(sK3,sK5) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1035]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_34,plain,
% 3.59/0.98      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_35,plain,
% 3.59/0.98      ( v2_struct_0(sK4) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_36,plain,
% 3.59/0.98      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_38,plain,
% 3.59/0.98      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_80,plain,
% 3.59/0.98      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_82,plain,
% 3.59/0.98      ( l1_pre_topc(sK5) != iProver_top
% 3.59/0.98      | l1_struct_0(sK5) = iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_80]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1760,plain,
% 3.59/0.98      ( m1_pre_topc(X0_44,sK2) != iProver_top
% 3.59/0.98      | l1_pre_topc(X0_44) = iProver_top
% 3.59/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1759]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1762,plain,
% 3.59/0.98      ( m1_pre_topc(sK5,sK2) != iProver_top
% 3.59/0.98      | l1_pre_topc(sK5) = iProver_top
% 3.59/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1760]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2101,plain,
% 3.59/0.98      ( l1_pre_topc(k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.59/0.98      | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_2100]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2115,plain,
% 3.59/0.98      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK4) ),
% 3.59/0.98      inference(resolution,[status(thm)],[c_1053,c_1043]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1817,plain,
% 3.59/0.98      ( l1_pre_topc(sK2) != iProver_top
% 3.59/0.98      | l1_pre_topc(sK4) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1646,c_1636]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1819,plain,
% 3.59/0.98      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK4) ),
% 3.59/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1817]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2190,plain,
% 3.59/0.98      ( l1_pre_topc(sK4) ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_2115,c_29,c_1819]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2202,plain,
% 3.59/0.98      ( l1_struct_0(sK4) ),
% 3.59/0.98      inference(resolution,[status(thm)],[c_2190,c_1054]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2203,plain,
% 3.59/0.98      ( l1_struct_0(sK4) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_2202]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2235,plain,
% 3.59/0.98      ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK4),sK2) != iProver_top
% 3.59/0.98      | l1_pre_topc(k1_tsep_1(sK2,sK3,sK4)) = iProver_top
% 3.59/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_2234]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2311,plain,
% 3.59/0.98      ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK4),sK2) = iProver_top
% 3.59/0.98      | m1_pre_topc(sK3,sK2) != iProver_top
% 3.59/0.98      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.59/0.98      | v2_struct_0(sK2) = iProver_top
% 3.59/0.98      | v2_struct_0(sK3) = iProver_top
% 3.59/0.98      | v2_struct_0(sK4) = iProver_top
% 3.59/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_2310]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_630,plain,
% 3.59/0.98      ( r1_tsep_1(X0,X1)
% 3.59/0.98      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | r1_tsep_1(sK5,sK4)
% 3.59/0.98      | sK5 != X1
% 3.59/0.98      | sK2 != X2
% 3.59/0.98      | sK3 != X3
% 3.59/0.98      | sK4 != X0 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_432]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_631,plain,
% 3.59/0.98      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | r1_tsep_1(sK5,sK4)
% 3.59/0.98      | r1_tsep_1(sK4,sK5) ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_630]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1032,plain,
% 3.59/0.98      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | r1_tsep_1(sK5,sK4)
% 3.59/0.98      | r1_tsep_1(sK4,sK5) ),
% 3.59/0.98      inference(subtyping,[status(esa)],[c_631]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2364,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | r1_tsep_1(sK5,sK4)
% 3.59/0.98      | r1_tsep_1(sK4,sK5)
% 3.59/0.98      | ~ l1_struct_0(k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | ~ l1_struct_0(sK5) ),
% 3.59/0.98      inference(resolution,[status(thm)],[c_1046,c_1032]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2369,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) = iProver_top
% 3.59/0.98      | r1_tsep_1(sK5,sK4) = iProver_top
% 3.59/0.98      | r1_tsep_1(sK4,sK5) = iProver_top
% 3.59/0.98      | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.59/0.98      | l1_struct_0(sK5) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_2364]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2629,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,sK4)
% 3.59/0.98      | ~ r1_tsep_1(sK4,sK5)
% 3.59/0.98      | ~ l1_struct_0(sK5)
% 3.59/0.98      | ~ l1_struct_0(sK4) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1046]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2635,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,sK4) = iProver_top
% 3.59/0.98      | r1_tsep_1(sK4,sK5) != iProver_top
% 3.59/0.98      | l1_struct_0(sK5) != iProver_top
% 3.59/0.98      | l1_struct_0(sK4) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_2629]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2708,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,sK4) = iProver_top
% 3.59/0.98      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) = iProver_top ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_1654,c_31,c_32,c_33,c_34,c_35,c_36,c_38,c_82,c_1762,
% 3.59/0.98                 c_2101,c_2203,c_2235,c_2311,c_2369,c_2635]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2709,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) = iProver_top
% 3.59/0.98      | r1_tsep_1(sK5,sK4) = iProver_top ),
% 3.59/0.98      inference(renaming,[status(thm)],[c_2708]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_552,plain,
% 3.59/0.98      ( r1_tsep_1(X0,X1)
% 3.59/0.98      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK3)
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK4)
% 3.59/0.98      | sK5 != X1
% 3.59/0.98      | sK2 != X2
% 3.59/0.98      | sK3 != X0
% 3.59/0.98      | sK4 != X3 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_475]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_553,plain,
% 3.59/0.98      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK3)
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK4)
% 3.59/0.98      | r1_tsep_1(sK3,sK5) ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_552]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1036,plain,
% 3.59/0.98      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK3)
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK4)
% 3.59/0.98      | r1_tsep_1(sK3,sK5) ),
% 3.59/0.98      inference(subtyping,[status(esa)],[c_553]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1653,plain,
% 3.59/0.98      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) = iProver_top
% 3.59/0.98      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.59/0.98      | r1_tsep_1(sK5,sK3) != iProver_top
% 3.59/0.98      | r1_tsep_1(sK5,sK4) != iProver_top
% 3.59/0.98      | r1_tsep_1(sK3,sK5) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1036]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1981,plain,
% 3.59/0.98      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) = iProver_top
% 3.59/0.98      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.59/0.98      | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.59/0.98      | l1_struct_0(sK5) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1980]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2531,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.59/0.98      | r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) = iProver_top ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_1653,c_31,c_32,c_33,c_34,c_35,c_36,c_38,c_82,c_1762,
% 3.59/0.98                 c_1981,c_2101,c_2235,c_2311]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2532,plain,
% 3.59/0.98      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) = iProver_top
% 3.59/0.98      | r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) != iProver_top ),
% 3.59/0.98      inference(renaming,[status(thm)],[c_2531]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2712,plain,
% 3.59/0.98      ( r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5) = iProver_top
% 3.59/0.98      | r1_tsep_1(sK5,sK4) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_2709,c_2532]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5174,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,sK4)
% 3.59/0.98      | ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
% 3.59/0.98      | ~ l1_struct_0(sK5)
% 3.59/0.98      | ~ l1_struct_0(sK4) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1051]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5175,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,sK4) = iProver_top
% 3.59/0.98      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) != iProver_top
% 3.59/0.98      | l1_struct_0(sK5) != iProver_top
% 3.59/0.98      | l1_struct_0(sK4) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_5174]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_0,plain,
% 3.59/0.98      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 3.59/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1057,plain,
% 3.59/0.98      ( r1_xboole_0(X0_45,X1_45)
% 3.59/0.98      | ~ r1_xboole_0(X0_45,k2_xboole_0(X2_45,X1_45)) ),
% 3.59/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1632,plain,
% 3.59/0.98      ( r1_xboole_0(X0_45,X1_45) = iProver_top
% 3.59/0.98      | r1_xboole_0(X0_45,k2_xboole_0(X2_45,X1_45)) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1057]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5591,plain,
% 3.59/0.98      ( r1_xboole_0(X0_45,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) != iProver_top
% 3.59/0.98      | r1_xboole_0(X0_45,u1_struct_0(sK4)) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_5588,c_1632]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5869,plain,
% 3.59/0.98      ( r1_tsep_1(X0_44,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.59/0.98      | r1_xboole_0(u1_struct_0(X0_44),u1_struct_0(sK4)) = iProver_top
% 3.59/0.98      | l1_struct_0(X0_44) != iProver_top
% 3.59/0.98      | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1639,c_5591]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5871,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.59/0.98      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) = iProver_top
% 3.59/0.98      | l1_struct_0(k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.59/0.98      | l1_struct_0(sK5) != iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_5869]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6317,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,sK4) = iProver_top ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_2712,c_31,c_32,c_33,c_34,c_35,c_36,c_38,c_82,c_1762,
% 3.59/0.98                 c_2101,c_2203,c_2235,c_2311,c_2709,c_5175,c_5871]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3016,plain,
% 3.59/0.98      ( ~ r1_tsep_1(sK5,sK4)
% 3.59/0.98      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
% 3.59/0.98      | ~ l1_struct_0(sK5)
% 3.59/0.98      | ~ l1_struct_0(sK4) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1050]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3025,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,sK4) != iProver_top
% 3.59/0.98      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) = iProver_top
% 3.59/0.98      | l1_struct_0(sK5) != iProver_top
% 3.59/0.98      | l1_struct_0(sK4) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_3016]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3017,plain,
% 3.59/0.98      ( ~ r1_tsep_1(sK5,sK4)
% 3.59/0.98      | r1_tsep_1(sK4,sK5)
% 3.59/0.98      | ~ l1_struct_0(sK5)
% 3.59/0.98      | ~ l1_struct_0(sK4) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1046]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3023,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,sK4) != iProver_top
% 3.59/0.98      | r1_tsep_1(sK4,sK5) = iProver_top
% 3.59/0.98      | l1_struct_0(sK5) != iProver_top
% 3.59/0.98      | l1_struct_0(sK4) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_3017]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3005,plain,
% 3.59/0.98      ( ~ r1_tsep_1(sK5,sK3)
% 3.59/0.98      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
% 3.59/0.98      | ~ l1_struct_0(sK5)
% 3.59/0.98      | ~ l1_struct_0(sK3) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1050]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3014,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,sK3) != iProver_top
% 3.59/0.98      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
% 3.59/0.98      | l1_struct_0(sK5) != iProver_top
% 3.59/0.98      | l1_struct_0(sK3) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_3005]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3006,plain,
% 3.59/0.98      ( ~ r1_tsep_1(sK5,sK3)
% 3.59/0.98      | r1_tsep_1(sK3,sK5)
% 3.59/0.98      | ~ l1_struct_0(sK5)
% 3.59/0.98      | ~ l1_struct_0(sK3) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1046]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3012,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,sK3) != iProver_top
% 3.59/0.98      | r1_tsep_1(sK3,sK5) = iProver_top
% 3.59/0.98      | l1_struct_0(sK5) != iProver_top
% 3.59/0.98      | l1_struct_0(sK3) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_3006]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_16,plain,
% 3.59/0.98      ( ~ sP0(X0,X1,X2,X3) | ~ r1_tsep_1(k1_tsep_1(X3,X2,X1),X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_19,negated_conjecture,
% 3.59/0.98      ( sP0(sK5,sK4,sK3,sK2)
% 3.59/0.98      | sP1(sK4,sK3,sK2,sK5)
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK3)
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK4)
% 3.59/0.98      | ~ r1_tsep_1(sK3,sK5)
% 3.59/0.98      | ~ r1_tsep_1(sK4,sK5) ),
% 3.59/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_493,plain,
% 3.59/0.98      ( sP0(sK5,sK4,sK3,sK2)
% 3.59/0.98      | ~ r1_tsep_1(X0,k1_tsep_1(X1,X2,X3))
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK3)
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK4)
% 3.59/0.98      | ~ r1_tsep_1(sK3,sK5)
% 3.59/0.98      | ~ r1_tsep_1(sK4,sK5)
% 3.59/0.98      | sK5 != X0
% 3.59/0.98      | sK2 != X1
% 3.59/0.98      | sK3 != X2
% 3.59/0.98      | sK4 != X3 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_494,plain,
% 3.59/0.98      ( sP0(sK5,sK4,sK3,sK2)
% 3.59/0.98      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK3)
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK4)
% 3.59/0.98      | ~ r1_tsep_1(sK3,sK5)
% 3.59/0.98      | ~ r1_tsep_1(sK4,sK5) ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_493]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_664,plain,
% 3.59/0.98      ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
% 3.59/0.98      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK3)
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK4)
% 3.59/0.98      | ~ r1_tsep_1(sK3,sK5)
% 3.59/0.98      | ~ r1_tsep_1(sK4,sK5)
% 3.59/0.98      | sK5 != X3
% 3.59/0.98      | sK2 != X0
% 3.59/0.98      | sK3 != X1
% 3.59/0.98      | sK4 != X2 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_494]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_665,plain,
% 3.59/0.98      ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK3)
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK4)
% 3.59/0.98      | ~ r1_tsep_1(sK3,sK5)
% 3.59/0.98      | ~ r1_tsep_1(sK4,sK5) ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_664]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1030,plain,
% 3.59/0.98      ( ~ r1_tsep_1(k1_tsep_1(sK2,sK3,sK4),sK5)
% 3.59/0.98      | ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK3)
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK4)
% 3.59/0.98      | ~ r1_tsep_1(sK3,sK5)
% 3.59/0.98      | ~ r1_tsep_1(sK4,sK5) ),
% 3.59/0.98      inference(subtyping,[status(esa)],[c_665]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2662,plain,
% 3.59/0.98      ( ~ r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4))
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK3)
% 3.59/0.98      | ~ r1_tsep_1(sK5,sK4)
% 3.59/0.98      | ~ r1_tsep_1(sK3,sK5)
% 3.59/0.98      | ~ r1_tsep_1(sK4,sK5) ),
% 3.59/0.98      inference(backward_subsumption_resolution,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_2649,c_1030]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2667,plain,
% 3.59/0.98      ( r1_tsep_1(sK5,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.59/0.98      | r1_tsep_1(sK5,sK3) != iProver_top
% 3.59/0.98      | r1_tsep_1(sK5,sK4) != iProver_top
% 3.59/0.98      | r1_tsep_1(sK3,sK5) != iProver_top
% 3.59/0.98      | r1_tsep_1(sK4,sK5) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_2662]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2297,plain,
% 3.59/0.98      ( l1_struct_0(sK3) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_2296]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(contradiction,plain,
% 3.59/0.98      ( $false ),
% 3.59/0.98      inference(minisat,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_6743,c_6554,c_6317,c_3025,c_3023,c_3014,c_3012,c_2667,
% 3.59/0.98                 c_2311,c_2297,c_2235,c_2203,c_2101,c_1762,c_82,c_38,
% 3.59/0.98                 c_36,c_35,c_34,c_33,c_32,c_31]) ).
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.59/0.98  
% 3.59/0.98  ------                               Statistics
% 3.59/0.98  
% 3.59/0.98  ------ Selected
% 3.59/0.98  
% 3.59/0.98  total_time:                             0.215
% 3.59/0.98  
%------------------------------------------------------------------------------
