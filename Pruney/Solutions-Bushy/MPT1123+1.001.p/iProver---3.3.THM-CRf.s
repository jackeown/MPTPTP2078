%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1123+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:56 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 578 expanded)
%              Number of clauses        :   88 ( 145 expanded)
%              Number of leaves         :   17 ( 162 expanded)
%              Depth                    :   22
%              Number of atoms          :  776 (5923 expanded)
%              Number of equality atoms :   42 (  62 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_xboole_0(X1,X3)
                          & r2_hidden(X2,X3)
                          & v3_pre_topc(X3,X0) ) )
                  & ~ v2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_pre_topc(X0,X1))
                <=> ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_xboole_0(X1,X3)
                            & r2_hidden(X2,X3)
                            & v3_pre_topc(X3,X0) ) )
                    & ~ v2_struct_0(X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | v2_struct_0(X0)
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | v2_struct_0(X0)
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | v2_struct_0(X0)
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(rectify,[],[f39])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( r1_xboole_0(X1,X3)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK8)
        & r2_hidden(X2,sK8)
        & v3_pre_topc(sK8,X0)
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( r1_xboole_0(X1,X3)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_struct_0(X0)
            | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
          & ( ( ! [X4] :
                  ( ~ r1_xboole_0(X1,X4)
                  | ~ r2_hidden(X2,X4)
                  | ~ v3_pre_topc(X4,X0)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              & ~ v2_struct_0(X0) )
            | r2_hidden(X2,k2_pre_topc(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ? [X3] :
              ( r1_xboole_0(X1,X3)
              & r2_hidden(sK7,X3)
              & v3_pre_topc(X3,X0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | v2_struct_0(X0)
          | ~ r2_hidden(sK7,k2_pre_topc(X0,X1)) )
        & ( ( ! [X4] :
                ( ~ r1_xboole_0(X1,X4)
                | ~ r2_hidden(sK7,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & ~ v2_struct_0(X0) )
          | r2_hidden(sK7,k2_pre_topc(X0,X1)) )
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | v2_struct_0(X0)
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( r1_xboole_0(sK6,X3)
                  & r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | v2_struct_0(X0)
              | ~ r2_hidden(X2,k2_pre_topc(X0,sK6)) )
            & ( ( ! [X4] :
                    ( ~ r1_xboole_0(sK6,X4)
                    | ~ r2_hidden(X2,X4)
                    | ~ v3_pre_topc(X4,X0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                & ~ v2_struct_0(X0) )
              | r2_hidden(X2,k2_pre_topc(X0,sK6)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0)
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & ( ( ! [X4] :
                        ( ~ r1_xboole_0(X1,X4)
                        | ~ r2_hidden(X2,X4)
                        | ~ v3_pre_topc(X4,X0)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,sK5)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5))) )
                | v2_struct_0(sK5)
                | ~ r2_hidden(X2,k2_pre_topc(sK5,X1)) )
              & ( ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,sK5)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK5))) )
                  & ~ v2_struct_0(sK5) )
                | r2_hidden(X2,k2_pre_topc(sK5,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK5)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) )
      & l1_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ( r1_xboole_0(sK6,sK8)
        & r2_hidden(sK7,sK8)
        & v3_pre_topc(sK8,sK5)
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) )
      | v2_struct_0(sK5)
      | ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6)) )
    & ( ( ! [X4] :
            ( ~ r1_xboole_0(sK6,X4)
            | ~ r2_hidden(sK7,X4)
            | ~ v3_pre_topc(X4,sK5)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK5))) )
        & ~ v2_struct_0(sK5) )
      | r2_hidden(sK7,k2_pre_topc(sK5,sK6)) )
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    & l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f40,f44,f43,f42,f41])).

fof(f71,plain,(
    ! [X4] :
      ( ~ r1_xboole_0(sK6,X4)
      | ~ r2_hidden(sK7,X4)
      | ~ v3_pre_topc(X4,sK5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK5)))
      | r2_hidden(sK7,k2_pre_topc(sK5,sK6)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( ( r2_hidden(X3,X2)
          <=> ! [X4] :
                ( ~ r1_xboole_0(X1,X4)
                | ~ r2_hidden(X3,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ r2_hidden(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ? [X4] :
                  ( r1_xboole_0(X1,X4)
                  & r2_hidden(X3,X4)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X3,X2) )
            & ( ! [X4] :
                  ( ~ r1_xboole_0(X1,X4)
                  | ~ r2_hidden(X3,X4)
                  | ~ v3_pre_topc(X4,X0)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X3,X2) )
            & r2_hidden(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ? [X4] :
                    ( r1_xboole_0(X1,X4)
                    & r2_hidden(X3,X4)
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X1,X4)
                    | ~ r2_hidden(X3,X4)
                    | ~ v3_pre_topc(X4,X0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ r2_hidden(X3,u1_struct_0(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ? [X4] :
                  ( r1_xboole_0(X1,X4)
                  & r2_hidden(X3,X4)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X3,X2) )
            & ( ! [X4] :
                  ( ~ r1_xboole_0(X1,X4)
                  | ~ r2_hidden(X3,X4)
                  | ~ v3_pre_topc(X4,X0)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X3,X2) )
            & r2_hidden(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ? [X4] :
                    ( r1_xboole_0(X1,X4)
                    & r2_hidden(X3,X4)
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X1,X4)
                    | ~ r2_hidden(X3,X4)
                    | ~ v3_pre_topc(X4,X0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ r2_hidden(X3,u1_struct_0(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ? [X4] :
                  ( r1_xboole_0(X0,X4)
                  & r2_hidden(X3,X4)
                  & v3_pre_topc(X4,X1)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X3,X2) )
            & ( ! [X5] :
                  ( ~ r1_xboole_0(X0,X5)
                  | ~ r2_hidden(X3,X5)
                  | ~ v3_pre_topc(X5,X1)
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
              | r2_hidden(X3,X2) )
            & r2_hidden(X3,u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ? [X7] :
                    ( r1_xboole_0(X0,X7)
                    & r2_hidden(X6,X7)
                    & v3_pre_topc(X7,X1)
                    & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) ) )
              & ( ! [X8] :
                    ( ~ r1_xboole_0(X0,X8)
                    | ~ r2_hidden(X6,X8)
                    | ~ v3_pre_topc(X8,X1)
                    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ r2_hidden(X6,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f32])).

fof(f36,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( r1_xboole_0(X0,X7)
          & r2_hidden(X6,X7)
          & v3_pre_topc(X7,X1)
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r1_xboole_0(X0,sK4(X0,X1,X6))
        & r2_hidden(X6,sK4(X0,X1,X6))
        & v3_pre_topc(sK4(X0,X1,X6),X1)
        & m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( r1_xboole_0(X0,X4)
          & r2_hidden(X3,X4)
          & v3_pre_topc(X4,X1)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r1_xboole_0(X0,sK3(X0,X1,X2))
        & r2_hidden(X3,sK3(X0,X1,X2))
        & v3_pre_topc(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( r1_xboole_0(X0,X4)
                & r2_hidden(X3,X4)
                & v3_pre_topc(X4,X1)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(X3,X2) )
          & ( ! [X5] :
                ( ~ r1_xboole_0(X0,X5)
                | ~ r2_hidden(X3,X5)
                | ~ v3_pre_topc(X5,X1)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(X3,X2) )
          & r2_hidden(X3,u1_struct_0(X1)) )
     => ( ( ? [X4] :
              ( r1_xboole_0(X0,X4)
              & r2_hidden(sK2(X0,X1,X2),X4)
              & v3_pre_topc(X4,X1)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( ~ r1_xboole_0(X0,X5)
              | ~ r2_hidden(sK2(X0,X1,X2),X5)
              | ~ v3_pre_topc(X5,X1)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK2(X0,X1,X2),X2) )
        & r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( r1_xboole_0(X0,sK3(X0,X1,X2))
              & r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2))
              & v3_pre_topc(sK3(X0,X1,X2),X1)
              & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ! [X5] :
                ( ~ r1_xboole_0(X0,X5)
                | ~ r2_hidden(sK2(X0,X1,X2),X5)
                | ~ v3_pre_topc(X5,X1)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK2(X0,X1,X2),X2) )
          & r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ( r1_xboole_0(X0,sK4(X0,X1,X6))
                  & r2_hidden(X6,sK4(X0,X1,X6))
                  & v3_pre_topc(sK4(X0,X1,X6),X1)
                  & m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1))) ) )
              & ( ! [X8] :
                    ( ~ r1_xboole_0(X0,X8)
                    | ~ r2_hidden(X6,X8)
                    | ~ v3_pre_topc(X8,X1)
                    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ r2_hidden(X6,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f33,f36,f35,f34])).

fof(f52,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | r1_xboole_0(X0,sK4(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f49,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f50,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | v3_pre_topc(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f51,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | r2_hidden(X6,sK4(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f48,plain,(
    ! [X6,X2,X0,X8,X1] :
      ( ~ r1_xboole_0(X0,X8)
      | ~ r2_hidden(X6,X8)
      | ~ v3_pre_topc(X8,X1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X6,X2)
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f67,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,
    ( ~ v2_struct_0(sK5)
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6)) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,
    ( r2_hidden(sK7,sK8)
    | v2_struct_0(sK5)
    | ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6)) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f62,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f68,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ( k2_pre_topc(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ( ( k2_pre_topc(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k2_pre_topc(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( k2_pre_topc(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k2_pre_topc(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f29])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k2_pre_topc(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
    ! [X2,X1] :
      ( sP0(X2,X1,k2_pre_topc(X1,X2))
      | ~ sP1(k2_pre_topc(X1,X2),X1,X2) ) ),
    inference(equality_resolution,[],[f46])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( r2_hidden(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( r1_xboole_0(X1,X4)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X0) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( ~ r1_xboole_0(X1,X4)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                    | ~ r2_hidden(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( ~ r1_xboole_0(X1,X4)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                    | ~ r2_hidden(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f12,f27,f26])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,
    ( r1_xboole_0(sK6,sK8)
    | v2_struct_0(sK5)
    | ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6)) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,
    ( v3_pre_topc(sK8,sK5)
    | v2_struct_0(sK5)
    | ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6)) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5)
    | ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6)) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_25,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(X0,sK5)
    | ~ r2_hidden(sK7,X0)
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ r1_xboole_0(sK6,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_4495,negated_conjecture,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(X0_48,sK5)
    | ~ r2_hidden(sK7,X0_48)
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ r1_xboole_0(sK6,X0_48) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_7798,plain,
    ( ~ m1_subset_1(sK4(X0_48,sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(sK4(X0_48,sK5,sK7),sK5)
    | ~ r2_hidden(sK7,sK4(X0_48,sK5,sK7))
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ r1_xboole_0(sK6,sK4(X0_48,sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_4495])).

cnf(c_7800,plain,
    ( ~ m1_subset_1(sK4(sK6,sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(sK4(sK6,sK5,sK7),sK5)
    | ~ r2_hidden(sK7,sK4(sK6,sK5,sK7))
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ r1_xboole_0(sK6,sK4(sK6,sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_7798])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | r1_xboole_0(X0,sK4(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4503,plain,
    ( ~ sP0(X0_48,X0_49,X1_48)
    | r2_hidden(X2_48,X1_48)
    | ~ r2_hidden(X2_48,u1_struct_0(X0_49))
    | r1_xboole_0(X0_48,sK4(X0_48,X0_49,X2_48)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_5351,plain,
    ( ~ sP0(X0_48,sK5,X1_48)
    | r2_hidden(sK7,X1_48)
    | ~ r2_hidden(sK7,u1_struct_0(sK5))
    | r1_xboole_0(X0_48,sK4(X0_48,sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_4503])).

cnf(c_7216,plain,
    ( ~ sP0(X0_48,sK5,k2_pre_topc(sK5,sK6))
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ r2_hidden(sK7,u1_struct_0(sK5))
    | r1_xboole_0(X0_48,sK4(X0_48,sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_5351])).

cnf(c_7233,plain,
    ( ~ sP0(sK6,sK5,k2_pre_topc(sK5,sK6))
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ r2_hidden(sK7,u1_struct_0(sK5))
    | r1_xboole_0(sK6,sK4(sK6,sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_7216])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2)
    | m1_subset_1(sK4(X0,X1,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4500,plain,
    ( ~ sP0(X0_48,X0_49,X1_48)
    | m1_subset_1(sK4(X0_48,X0_49,X2_48),k1_zfmisc_1(u1_struct_0(X0_49)))
    | r2_hidden(X2_48,X1_48)
    | ~ r2_hidden(X2_48,u1_struct_0(X0_49)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_5354,plain,
    ( ~ sP0(X0_48,sK5,X1_48)
    | m1_subset_1(sK4(X0_48,sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK7,X1_48)
    | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4500])).

cnf(c_7217,plain,
    ( ~ sP0(X0_48,sK5,k2_pre_topc(sK5,sK6))
    | m1_subset_1(sK4(X0_48,sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_5354])).

cnf(c_7229,plain,
    ( ~ sP0(sK6,sK5,k2_pre_topc(sK5,sK6))
    | m1_subset_1(sK4(sK6,sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_7217])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2)
    | v3_pre_topc(sK4(X0,X1,X3),X1)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_4501,plain,
    ( ~ sP0(X0_48,X0_49,X1_48)
    | v3_pre_topc(sK4(X0_48,X0_49,X2_48),X0_49)
    | r2_hidden(X2_48,X1_48)
    | ~ r2_hidden(X2_48,u1_struct_0(X0_49)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_5353,plain,
    ( ~ sP0(X0_48,sK5,X1_48)
    | v3_pre_topc(sK4(X0_48,sK5,sK7),sK5)
    | r2_hidden(sK7,X1_48)
    | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4501])).

cnf(c_7218,plain,
    ( ~ sP0(X0_48,sK5,k2_pre_topc(sK5,sK6))
    | v3_pre_topc(sK4(X0_48,sK5,sK7),sK5)
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_5353])).

cnf(c_7225,plain,
    ( ~ sP0(sK6,sK5,k2_pre_topc(sK5,sK6))
    | v3_pre_topc(sK4(sK6,sK5,sK7),sK5)
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_7218])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_hidden(X3,X2)
    | r2_hidden(X3,sK4(X0,X1,X3))
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4502,plain,
    ( ~ sP0(X0_48,X0_49,X1_48)
    | r2_hidden(X2_48,X1_48)
    | r2_hidden(X2_48,sK4(X0_48,X0_49,X2_48))
    | ~ r2_hidden(X2_48,u1_struct_0(X0_49)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_5352,plain,
    ( ~ sP0(X0_48,sK5,X1_48)
    | r2_hidden(sK7,X1_48)
    | r2_hidden(sK7,sK4(X0_48,sK5,sK7))
    | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4502])).

cnf(c_7219,plain,
    ( ~ sP0(X0_48,sK5,k2_pre_topc(sK5,sK6))
    | r2_hidden(sK7,sK4(X0_48,sK5,sK7))
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_5352])).

cnf(c_7221,plain,
    ( ~ sP0(sK6,sK5,k2_pre_topc(sK5,sK6))
    | r2_hidden(sK7,sK4(sK6,sK5,sK7))
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_7219])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X3,X1)
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | ~ r1_xboole_0(X0,X3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4499,plain,
    ( ~ sP0(X0_48,X0_49,X1_48)
    | ~ m1_subset_1(X2_48,k1_zfmisc_1(u1_struct_0(X0_49)))
    | ~ v3_pre_topc(X2_48,X0_49)
    | ~ r2_hidden(X3_48,X2_48)
    | ~ r2_hidden(X3_48,X1_48)
    | ~ r2_hidden(X3_48,u1_struct_0(X0_49))
    | ~ r1_xboole_0(X0_48,X2_48) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_6033,plain,
    ( ~ sP0(X0_48,sK5,X1_48)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(sK8,sK5)
    | ~ r2_hidden(X2_48,X1_48)
    | ~ r2_hidden(X2_48,u1_struct_0(sK5))
    | ~ r2_hidden(X2_48,sK8)
    | ~ r1_xboole_0(X0_48,sK8) ),
    inference(instantiation,[status(thm)],[c_4499])).

cnf(c_6265,plain,
    ( ~ sP0(X0_48,sK5,X1_48)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(sK8,sK5)
    | ~ r2_hidden(sK7,X1_48)
    | ~ r2_hidden(sK7,u1_struct_0(sK5))
    | ~ r2_hidden(sK7,sK8)
    | ~ r1_xboole_0(X0_48,sK8) ),
    inference(instantiation,[status(thm)],[c_6033])).

cnf(c_6583,plain,
    ( ~ sP0(X0_48,sK5,k2_pre_topc(sK5,X0_48))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(sK8,sK5)
    | ~ r2_hidden(sK7,k2_pre_topc(sK5,X0_48))
    | ~ r2_hidden(sK7,u1_struct_0(sK5))
    | ~ r2_hidden(sK7,sK8)
    | ~ r1_xboole_0(X0_48,sK8) ),
    inference(instantiation,[status(thm)],[c_6265])).

cnf(c_6585,plain,
    ( ~ sP0(sK6,sK5,k2_pre_topc(sK5,sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(sK8,sK5)
    | ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ r2_hidden(sK7,u1_struct_0(sK5))
    | ~ r2_hidden(sK7,sK8)
    | ~ r1_xboole_0(sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_6583])).

cnf(c_17,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_15,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_357,plain,
    ( l1_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_358,plain,
    ( l1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_373,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_358])).

cnf(c_374,plain,
    ( v2_struct_0(sK5)
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_529,plain,
    ( r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_374,c_26])).

cnf(c_4489,plain,
    ( r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_529])).

cnf(c_5023,plain,
    ( r2_hidden(sK7,k2_pre_topc(sK5,sK6)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4489])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | r2_hidden(sK7,sK8)
    | v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_16,plain,
    ( ~ v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_383,plain,
    ( ~ v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_358])).

cnf(c_384,plain,
    ( ~ v2_struct_0(sK5)
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_564,plain,
    ( ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | r2_hidden(sK7,sK8)
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_22,c_384])).

cnf(c_4486,plain,
    ( ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | r2_hidden(sK7,sK8)
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_564])).

cnf(c_5026,plain,
    ( r2_hidden(sK7,k2_pre_topc(sK5,sK6)) != iProver_top
    | r2_hidden(sK7,sK8) = iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4486])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_530,plain,
    ( r2_hidden(sK7,k2_pre_topc(sK5,sK6)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_529])).

cnf(c_565,plain,
    ( r2_hidden(sK7,k2_pre_topc(sK5,sK6)) != iProver_top
    | r2_hidden(sK7,sK8) = iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_564])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_330,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_29])).

cnf(c_331,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(k2_pre_topc(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_4492,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(k2_pre_topc(sK5,X0_48),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(subtyping,[status(esa)],[c_331])).

cnf(c_4576,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK5,X0_48),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4492])).

cnf(c_4578,plain,
    ( m1_subset_1(k2_pre_topc(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4576])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_4497,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
    | ~ r2_hidden(X2_48,X0_48)
    | ~ v1_xboole_0(X1_48) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_5544,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1_48,X0_48)
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4497])).

cnf(c_5746,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_5544])).

cnf(c_5747,plain,
    ( m1_subset_1(k2_pre_topc(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5746])).

cnf(c_5778,plain,
    ( r2_hidden(sK7,sK8) = iProver_top
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5026,c_31,c_530,c_565,c_4578,c_5747])).

cnf(c_5779,plain,
    ( r2_hidden(sK7,k2_pre_topc(sK5,sK6)) != iProver_top
    | r2_hidden(sK7,sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_5778])).

cnf(c_5785,plain,
    ( r2_hidden(sK7,sK8) = iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5023,c_5779])).

cnf(c_5919,plain,
    ( v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5785,c_31,c_530,c_4578,c_5747])).

cnf(c_5921,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5919])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4498,plain,
    ( ~ m1_subset_1(X0_48,X1_48)
    | r2_hidden(X0_48,X1_48)
    | v1_xboole_0(X1_48) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_5253,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | r2_hidden(sK7,u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4498])).

cnf(c_1,plain,
    ( ~ sP1(k2_pre_topc(X0,X1),X0,X1)
    | sP0(X1,X0,k2_pre_topc(X0,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_13,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_342,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_343,plain,
    ( sP1(X0,sK5,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_417,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))
    | X3 != X0
    | k2_pre_topc(X1,X0) != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_343])).

cnf(c_418,plain,
    ( sP0(X0,sK5,k2_pre_topc(sK5,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(k2_pre_topc(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_422,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | sP0(X0,sK5,k2_pre_topc(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_418,c_331])).

cnf(c_423,plain,
    ( sP0(X0,sK5,k2_pre_topc(sK5,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(renaming,[status(thm)],[c_422])).

cnf(c_4490,plain,
    ( sP0(X0_48,sK5,k2_pre_topc(sK5,X0_48))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(subtyping,[status(esa)],[c_423])).

cnf(c_4583,plain,
    ( sP0(sK6,sK5,k2_pre_topc(sK5,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_4490])).

cnf(c_55,plain,
    ( l1_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_52,plain,
    ( ~ v2_struct_0(sK5)
    | v1_xboole_0(u1_struct_0(sK5))
    | ~ l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | r1_xboole_0(sK6,sK8)
    | v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_23,negated_conjecture,
    ( v3_pre_topc(sK8,sK5)
    | ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f69])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7800,c_7233,c_7229,c_7225,c_7221,c_6585,c_5921,c_5253,c_4583,c_55,c_52,c_21,c_22,c_23,c_24,c_27,c_28,c_29])).


%------------------------------------------------------------------------------
