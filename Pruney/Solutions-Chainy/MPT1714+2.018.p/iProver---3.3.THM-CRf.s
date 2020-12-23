%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:59 EST 2020

% Result     : Theorem 11.02s
% Output     : CNFRefutation 11.02s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 691 expanded)
%              Number of clauses        :   88 ( 191 expanded)
%              Number of leaves         :   23 ( 197 expanded)
%              Depth                    :   23
%              Number of atoms          :  704 (5087 expanded)
%              Number of equality atoms :  162 ( 215 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f34])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2] :
            ( ( r2_hidden(X2,u1_pre_topc(X1))
            <=> ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X0))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,u1_pre_topc(X1)) )
            & ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,u1_pre_topc(X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & r2_hidden(X3,u1_pre_topc(X0))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X0))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,u1_pre_topc(X1)) )
            & ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,u1_pre_topc(X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & r2_hidden(X3,u1_pre_topc(X0))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X1))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X2,u1_pre_topc(X0)) )
            & ( ? [X4] :
                  ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
                  & r2_hidden(X4,u1_pre_topc(X1))
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              | r2_hidden(X2,u1_pre_topc(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ? [X7] :
                      ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
                      & r2_hidden(X7,u1_pre_topc(X1))
                      & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f42,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK5(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(X2,u1_pre_topc(X0)) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
                & r2_hidden(X4,u1_pre_topc(X1))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(X2,u1_pre_topc(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK4(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X1))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) )
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1)
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) )
          & ( ( k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0)) = sK4(X0,X1)
              & r2_hidden(sK5(X0,X1),u1_pre_topc(X1))
              & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) )
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5
                    & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1))
                    & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f42,f41,f40])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f75,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f13,plain,(
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
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f14,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ! [X3] :
                    ( m1_pre_topc(X3,X0)
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( r1_tsep_1(X3,X2)
            | r1_tsep_1(X2,X3) )
          & ( ~ r1_tsep_1(X3,X1)
            | ~ r1_tsep_1(X1,X3) )
          & m1_pre_topc(X1,X2)
          & m1_pre_topc(X3,X0) )
     => ( ( r1_tsep_1(sK10,X2)
          | r1_tsep_1(X2,sK10) )
        & ( ~ r1_tsep_1(sK10,X1)
          | ~ r1_tsep_1(X1,sK10) )
        & m1_pre_topc(X1,X2)
        & m1_pre_topc(sK10,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & ( ~ r1_tsep_1(X3,X1)
                | ~ r1_tsep_1(X1,X3) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X3,X0) )
          & m1_pre_topc(X2,X0) )
     => ( ? [X3] :
            ( ( r1_tsep_1(X3,sK9)
              | r1_tsep_1(sK9,X3) )
            & ( ~ r1_tsep_1(X3,X1)
              | ~ r1_tsep_1(X1,X3) )
            & m1_pre_topc(X1,sK9)
            & m1_pre_topc(X3,X0) )
        & m1_pre_topc(sK9,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & ( ~ r1_tsep_1(X3,sK8)
                  | ~ r1_tsep_1(sK8,X3) )
                & m1_pre_topc(sK8,X2)
                & m1_pre_topc(X3,X0) )
            & m1_pre_topc(X2,X0) )
        & m1_pre_topc(sK8,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0) )
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK7) )
              & m1_pre_topc(X2,sK7) )
          & m1_pre_topc(X1,sK7) )
      & l1_pre_topc(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( r1_tsep_1(sK10,sK9)
      | r1_tsep_1(sK9,sK10) )
    & ( ~ r1_tsep_1(sK10,sK8)
      | ~ r1_tsep_1(sK8,sK10) )
    & m1_pre_topc(sK8,sK9)
    & m1_pre_topc(sK10,sK7)
    & m1_pre_topc(sK9,sK7)
    & m1_pre_topc(sK8,sK7)
    & l1_pre_topc(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f25,f48,f47,f46,f45])).

fof(f81,plain,(
    m1_pre_topc(sK9,sK7) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f18,f27,f26])).

fof(f73,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f83,plain,(
    m1_pre_topc(sK8,sK9) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f74,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,
    ( r1_tsep_1(sK10,sK9)
    | r1_tsep_1(sK9,sK10) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f82,plain,(
    m1_pre_topc(sK10,sK7) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,
    ( ~ r1_tsep_1(sK10,sK8)
    | ~ r1_tsep_1(sK8,sK10) ),
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1602,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_442,plain,
    ( ~ sP0(X0,X1)
    | k3_xboole_0(X2,X3) = X2
    | k2_struct_0(X1) != X3
    | k2_struct_0(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_443,plain,
    ( ~ sP0(X0,X1)
    | k3_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_33,negated_conjecture,
    ( m1_pre_topc(sK9,sK7) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_649,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK7 != X0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_650,plain,
    ( ~ l1_pre_topc(sK7)
    | l1_pre_topc(sK9) ),
    inference(unflattening,[status(thm)],[c_649])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_652,plain,
    ( l1_pre_topc(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_650,c_35])).

cnf(c_23,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_12,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_394,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_23,c_12])).

cnf(c_398,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X0,X1)
    | sP0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_25])).

cnf(c_399,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_398])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK8,sK9) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_596,plain,
    ( sP0(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK8 != X0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_399,c_31])).

cnf(c_597,plain,
    ( sP0(sK8,sK9)
    | ~ l1_pre_topc(sK9) ),
    inference(unflattening,[status(thm)],[c_596])).

cnf(c_659,plain,
    ( sP0(sK8,sK9) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_652,c_597])).

cnf(c_916,plain,
    ( k3_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X0)
    | sK8 != X0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_443,c_659])).

cnf(c_917,plain,
    ( k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) = k2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_916])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1606,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2533,plain,
    ( r2_hidden(X0,k2_struct_0(sK8)) != iProver_top
    | r2_hidden(X0,k2_struct_0(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_917,c_1606])).

cnf(c_2996,plain,
    ( r1_xboole_0(k2_struct_0(sK8),X0) = iProver_top
    | r2_hidden(sK3(k2_struct_0(sK8),X0),k2_struct_0(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1602,c_2533])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK3(X0,X1),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1603,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_24,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_705,plain,
    ( l1_struct_0(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_652])).

cnf(c_706,plain,
    ( l1_struct_0(sK9) ),
    inference(unflattening,[status(thm)],[c_705])).

cnf(c_1593,plain,
    ( l1_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_10,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1601,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2012,plain,
    ( u1_struct_0(sK9) = k2_struct_0(sK9) ),
    inference(superposition,[status(thm)],[c_1593,c_1601])).

cnf(c_27,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1599,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3284,plain,
    ( r1_tsep_1(sK9,X0) != iProver_top
    | r1_xboole_0(k2_struct_0(sK9),u1_struct_0(X0)) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_2012,c_1599])).

cnf(c_707,plain,
    ( l1_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_17768,plain,
    ( l1_struct_0(X0) != iProver_top
    | r1_xboole_0(k2_struct_0(sK9),u1_struct_0(X0)) = iProver_top
    | r1_tsep_1(sK9,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3284,c_707])).

cnf(c_17769,plain,
    ( r1_tsep_1(sK9,X0) != iProver_top
    | r1_xboole_0(k2_struct_0(sK9),u1_struct_0(X0)) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_17768])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1604,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_17778,plain,
    ( r1_tsep_1(sK9,X0) != iProver_top
    | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X1,k2_struct_0(sK9)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17769,c_1604])).

cnf(c_32743,plain,
    ( r1_tsep_1(sK9,X0) != iProver_top
    | r1_xboole_0(X1,u1_struct_0(X0)) = iProver_top
    | r2_hidden(sK3(X1,u1_struct_0(X0)),k2_struct_0(sK9)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1603,c_17778])).

cnf(c_46725,plain,
    ( r1_tsep_1(sK9,X0) != iProver_top
    | r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X0)) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2996,c_32743])).

cnf(c_46769,plain,
    ( r1_tsep_1(sK9,sK10) != iProver_top
    | r1_xboole_0(k2_struct_0(sK8),u1_struct_0(sK10)) = iProver_top
    | l1_struct_0(sK10) != iProver_top ),
    inference(instantiation,[status(thm)],[c_46725])).

cnf(c_29,negated_conjecture,
    ( r1_tsep_1(sK9,sK10)
    | r1_tsep_1(sK10,sK9) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1597,plain,
    ( r1_tsep_1(sK9,sK10) = iProver_top
    | r1_tsep_1(sK10,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1598,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_tsep_1(X1,X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2644,plain,
    ( r1_tsep_1(sK10,sK9) = iProver_top
    | l1_struct_0(sK9) != iProver_top
    | l1_struct_0(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_1597,c_1598])).

cnf(c_36,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_51,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_53,plain,
    ( l1_pre_topc(sK10) != iProver_top
    | l1_struct_0(sK10) = iProver_top ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK10,sK7) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_627,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK7 != X0
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_32])).

cnf(c_628,plain,
    ( ~ l1_pre_topc(sK7)
    | l1_pre_topc(sK10) ),
    inference(unflattening,[status(thm)],[c_627])).

cnf(c_629,plain,
    ( l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_628])).

cnf(c_2907,plain,
    ( r1_tsep_1(sK10,sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2644,c_36,c_53,c_629,c_707])).

cnf(c_2911,plain,
    ( r1_tsep_1(sK9,sK10) = iProver_top
    | l1_struct_0(sK9) != iProver_top
    | l1_struct_0(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_2907,c_1598])).

cnf(c_1261,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2781,plain,
    ( u1_struct_0(sK10) = u1_struct_0(sK10) ),
    inference(instantiation,[status(thm)],[c_1261])).

cnf(c_1265,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1662,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10))
    | u1_struct_0(sK8) != X0
    | u1_struct_0(sK10) != X1 ),
    inference(instantiation,[status(thm)],[c_1265])).

cnf(c_1733,plain,
    ( r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10))
    | ~ r1_xboole_0(k2_struct_0(sK8),X0)
    | u1_struct_0(sK8) != k2_struct_0(sK8)
    | u1_struct_0(sK10) != X0 ),
    inference(instantiation,[status(thm)],[c_1662])).

cnf(c_2089,plain,
    ( r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10))
    | ~ r1_xboole_0(k2_struct_0(sK8),u1_struct_0(sK10))
    | u1_struct_0(sK8) != k2_struct_0(sK8)
    | u1_struct_0(sK10) != u1_struct_0(sK10) ),
    inference(instantiation,[status(thm)],[c_1733])).

cnf(c_2092,plain,
    ( u1_struct_0(sK8) != k2_struct_0(sK8)
    | u1_struct_0(sK10) != u1_struct_0(sK10)
    | r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10)) = iProver_top
    | r1_xboole_0(k2_struct_0(sK8),u1_struct_0(sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2089])).

cnf(c_1879,plain,
    ( ~ l1_struct_0(sK8)
    | u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1670,plain,
    ( ~ r1_tsep_1(sK8,sK10)
    | r1_tsep_1(sK10,sK8)
    | ~ l1_struct_0(sK8)
    | ~ l1_struct_0(sK10) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1671,plain,
    ( r1_tsep_1(sK8,sK10) != iProver_top
    | r1_tsep_1(sK10,sK8) = iProver_top
    | l1_struct_0(sK8) != iProver_top
    | l1_struct_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1670])).

cnf(c_30,negated_conjecture,
    ( ~ r1_tsep_1(sK8,sK10)
    | ~ r1_tsep_1(sK10,sK8) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1596,plain,
    ( r1_tsep_1(sK8,sK10) != iProver_top
    | r1_tsep_1(sK10,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_41,plain,
    ( r1_tsep_1(sK8,sK10) != iProver_top
    | r1_tsep_1(sK10,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_606,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK8 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_31])).

cnf(c_607,plain,
    ( l1_pre_topc(sK8)
    | ~ l1_pre_topc(sK9) ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_660,plain,
    ( l1_pre_topc(sK8) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_652,c_607])).

cnf(c_712,plain,
    ( l1_struct_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_660])).

cnf(c_713,plain,
    ( l1_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_712])).

cnf(c_714,plain,
    ( l1_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_1639,plain,
    ( r1_tsep_1(sK8,sK10)
    | ~ r1_tsep_1(sK10,sK8)
    | ~ l1_struct_0(sK8)
    | ~ l1_struct_0(sK10) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1640,plain,
    ( r1_tsep_1(sK8,sK10) = iProver_top
    | r1_tsep_1(sK10,sK8) != iProver_top
    | l1_struct_0(sK8) != iProver_top
    | l1_struct_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1639])).

cnf(c_1648,plain,
    ( r1_tsep_1(sK10,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1596,c_36,c_41,c_53,c_629,c_714,c_1640])).

cnf(c_26,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1636,plain,
    ( r1_tsep_1(sK8,sK10)
    | ~ r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10))
    | ~ l1_struct_0(sK8)
    | ~ l1_struct_0(sK10) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1637,plain,
    ( r1_tsep_1(sK8,sK10) = iProver_top
    | r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10)) != iProver_top
    | l1_struct_0(sK8) != iProver_top
    | l1_struct_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1636])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_46769,c_2911,c_2781,c_2092,c_1879,c_1671,c_1648,c_1637,c_714,c_713,c_707,c_629,c_53,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:15:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 11.02/1.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.02/1.97  
% 11.02/1.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.02/1.97  
% 11.02/1.97  ------  iProver source info
% 11.02/1.97  
% 11.02/1.97  git: date: 2020-06-30 10:37:57 +0100
% 11.02/1.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.02/1.97  git: non_committed_changes: false
% 11.02/1.97  git: last_make_outside_of_git: false
% 11.02/1.97  
% 11.02/1.97  ------ 
% 11.02/1.97  
% 11.02/1.97  ------ Input Options
% 11.02/1.97  
% 11.02/1.97  --out_options                           all
% 11.02/1.97  --tptp_safe_out                         true
% 11.02/1.97  --problem_path                          ""
% 11.02/1.97  --include_path                          ""
% 11.02/1.97  --clausifier                            res/vclausify_rel
% 11.02/1.97  --clausifier_options                    ""
% 11.02/1.97  --stdin                                 false
% 11.02/1.97  --stats_out                             all
% 11.02/1.97  
% 11.02/1.97  ------ General Options
% 11.02/1.97  
% 11.02/1.97  --fof                                   false
% 11.02/1.97  --time_out_real                         305.
% 11.02/1.97  --time_out_virtual                      -1.
% 11.02/1.97  --symbol_type_check                     false
% 11.02/1.97  --clausify_out                          false
% 11.02/1.97  --sig_cnt_out                           false
% 11.02/1.97  --trig_cnt_out                          false
% 11.02/1.97  --trig_cnt_out_tolerance                1.
% 11.02/1.97  --trig_cnt_out_sk_spl                   false
% 11.02/1.97  --abstr_cl_out                          false
% 11.02/1.97  
% 11.02/1.97  ------ Global Options
% 11.02/1.97  
% 11.02/1.97  --schedule                              default
% 11.02/1.97  --add_important_lit                     false
% 11.02/1.97  --prop_solver_per_cl                    1000
% 11.02/1.97  --min_unsat_core                        false
% 11.02/1.97  --soft_assumptions                      false
% 11.02/1.97  --soft_lemma_size                       3
% 11.02/1.97  --prop_impl_unit_size                   0
% 11.02/1.97  --prop_impl_unit                        []
% 11.02/1.97  --share_sel_clauses                     true
% 11.02/1.97  --reset_solvers                         false
% 11.02/1.97  --bc_imp_inh                            [conj_cone]
% 11.02/1.97  --conj_cone_tolerance                   3.
% 11.02/1.97  --extra_neg_conj                        none
% 11.02/1.97  --large_theory_mode                     true
% 11.02/1.97  --prolific_symb_bound                   200
% 11.02/1.97  --lt_threshold                          2000
% 11.02/1.97  --clause_weak_htbl                      true
% 11.02/1.97  --gc_record_bc_elim                     false
% 11.02/1.97  
% 11.02/1.97  ------ Preprocessing Options
% 11.02/1.97  
% 11.02/1.97  --preprocessing_flag                    true
% 11.02/1.97  --time_out_prep_mult                    0.1
% 11.02/1.97  --splitting_mode                        input
% 11.02/1.97  --splitting_grd                         true
% 11.02/1.97  --splitting_cvd                         false
% 11.02/1.97  --splitting_cvd_svl                     false
% 11.02/1.97  --splitting_nvd                         32
% 11.02/1.97  --sub_typing                            true
% 11.02/1.97  --prep_gs_sim                           true
% 11.02/1.97  --prep_unflatten                        true
% 11.02/1.97  --prep_res_sim                          true
% 11.02/1.97  --prep_upred                            true
% 11.02/1.97  --prep_sem_filter                       exhaustive
% 11.02/1.97  --prep_sem_filter_out                   false
% 11.02/1.97  --pred_elim                             true
% 11.02/1.97  --res_sim_input                         true
% 11.02/1.97  --eq_ax_congr_red                       true
% 11.02/1.97  --pure_diseq_elim                       true
% 11.02/1.97  --brand_transform                       false
% 11.02/1.97  --non_eq_to_eq                          false
% 11.02/1.97  --prep_def_merge                        true
% 11.02/1.97  --prep_def_merge_prop_impl              false
% 11.02/1.97  --prep_def_merge_mbd                    true
% 11.02/1.97  --prep_def_merge_tr_red                 false
% 11.02/1.97  --prep_def_merge_tr_cl                  false
% 11.02/1.97  --smt_preprocessing                     true
% 11.02/1.97  --smt_ac_axioms                         fast
% 11.02/1.97  --preprocessed_out                      false
% 11.02/1.97  --preprocessed_stats                    false
% 11.02/1.97  
% 11.02/1.97  ------ Abstraction refinement Options
% 11.02/1.97  
% 11.02/1.97  --abstr_ref                             []
% 11.02/1.97  --abstr_ref_prep                        false
% 11.02/1.97  --abstr_ref_until_sat                   false
% 11.02/1.97  --abstr_ref_sig_restrict                funpre
% 11.02/1.97  --abstr_ref_af_restrict_to_split_sk     false
% 11.02/1.97  --abstr_ref_under                       []
% 11.02/1.97  
% 11.02/1.97  ------ SAT Options
% 11.02/1.97  
% 11.02/1.97  --sat_mode                              false
% 11.02/1.97  --sat_fm_restart_options                ""
% 11.02/1.97  --sat_gr_def                            false
% 11.02/1.97  --sat_epr_types                         true
% 11.02/1.97  --sat_non_cyclic_types                  false
% 11.02/1.97  --sat_finite_models                     false
% 11.02/1.97  --sat_fm_lemmas                         false
% 11.02/1.97  --sat_fm_prep                           false
% 11.02/1.97  --sat_fm_uc_incr                        true
% 11.02/1.98  --sat_out_model                         small
% 11.02/1.98  --sat_out_clauses                       false
% 11.02/1.98  
% 11.02/1.98  ------ QBF Options
% 11.02/1.98  
% 11.02/1.98  --qbf_mode                              false
% 11.02/1.98  --qbf_elim_univ                         false
% 11.02/1.98  --qbf_dom_inst                          none
% 11.02/1.98  --qbf_dom_pre_inst                      false
% 11.02/1.98  --qbf_sk_in                             false
% 11.02/1.98  --qbf_pred_elim                         true
% 11.02/1.98  --qbf_split                             512
% 11.02/1.98  
% 11.02/1.98  ------ BMC1 Options
% 11.02/1.98  
% 11.02/1.98  --bmc1_incremental                      false
% 11.02/1.98  --bmc1_axioms                           reachable_all
% 11.02/1.98  --bmc1_min_bound                        0
% 11.02/1.98  --bmc1_max_bound                        -1
% 11.02/1.98  --bmc1_max_bound_default                -1
% 11.02/1.98  --bmc1_symbol_reachability              true
% 11.02/1.98  --bmc1_property_lemmas                  false
% 11.02/1.98  --bmc1_k_induction                      false
% 11.02/1.98  --bmc1_non_equiv_states                 false
% 11.02/1.98  --bmc1_deadlock                         false
% 11.02/1.98  --bmc1_ucm                              false
% 11.02/1.98  --bmc1_add_unsat_core                   none
% 11.02/1.98  --bmc1_unsat_core_children              false
% 11.02/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.02/1.98  --bmc1_out_stat                         full
% 11.02/1.98  --bmc1_ground_init                      false
% 11.02/1.98  --bmc1_pre_inst_next_state              false
% 11.02/1.98  --bmc1_pre_inst_state                   false
% 11.02/1.98  --bmc1_pre_inst_reach_state             false
% 11.02/1.98  --bmc1_out_unsat_core                   false
% 11.02/1.98  --bmc1_aig_witness_out                  false
% 11.02/1.98  --bmc1_verbose                          false
% 11.02/1.98  --bmc1_dump_clauses_tptp                false
% 11.02/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.02/1.98  --bmc1_dump_file                        -
% 11.02/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.02/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.02/1.98  --bmc1_ucm_extend_mode                  1
% 11.02/1.98  --bmc1_ucm_init_mode                    2
% 11.02/1.98  --bmc1_ucm_cone_mode                    none
% 11.02/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.02/1.98  --bmc1_ucm_relax_model                  4
% 11.02/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.02/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.02/1.98  --bmc1_ucm_layered_model                none
% 11.02/1.98  --bmc1_ucm_max_lemma_size               10
% 11.02/1.98  
% 11.02/1.98  ------ AIG Options
% 11.02/1.98  
% 11.02/1.98  --aig_mode                              false
% 11.02/1.98  
% 11.02/1.98  ------ Instantiation Options
% 11.02/1.98  
% 11.02/1.98  --instantiation_flag                    true
% 11.02/1.98  --inst_sos_flag                         true
% 11.02/1.98  --inst_sos_phase                        true
% 11.02/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.02/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.02/1.98  --inst_lit_sel_side                     num_symb
% 11.02/1.98  --inst_solver_per_active                1400
% 11.02/1.98  --inst_solver_calls_frac                1.
% 11.02/1.98  --inst_passive_queue_type               priority_queues
% 11.02/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.02/1.98  --inst_passive_queues_freq              [25;2]
% 11.02/1.98  --inst_dismatching                      true
% 11.02/1.98  --inst_eager_unprocessed_to_passive     true
% 11.02/1.98  --inst_prop_sim_given                   true
% 11.02/1.98  --inst_prop_sim_new                     false
% 11.02/1.98  --inst_subs_new                         false
% 11.02/1.98  --inst_eq_res_simp                      false
% 11.02/1.98  --inst_subs_given                       false
% 11.02/1.98  --inst_orphan_elimination               true
% 11.02/1.98  --inst_learning_loop_flag               true
% 11.02/1.98  --inst_learning_start                   3000
% 11.02/1.98  --inst_learning_factor                  2
% 11.02/1.98  --inst_start_prop_sim_after_learn       3
% 11.02/1.98  --inst_sel_renew                        solver
% 11.02/1.98  --inst_lit_activity_flag                true
% 11.02/1.98  --inst_restr_to_given                   false
% 11.02/1.98  --inst_activity_threshold               500
% 11.02/1.98  --inst_out_proof                        true
% 11.02/1.98  
% 11.02/1.98  ------ Resolution Options
% 11.02/1.98  
% 11.02/1.98  --resolution_flag                       true
% 11.02/1.98  --res_lit_sel                           adaptive
% 11.02/1.98  --res_lit_sel_side                      none
% 11.02/1.98  --res_ordering                          kbo
% 11.02/1.98  --res_to_prop_solver                    active
% 11.02/1.98  --res_prop_simpl_new                    false
% 11.02/1.98  --res_prop_simpl_given                  true
% 11.02/1.98  --res_passive_queue_type                priority_queues
% 11.02/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.02/1.98  --res_passive_queues_freq               [15;5]
% 11.02/1.98  --res_forward_subs                      full
% 11.02/1.98  --res_backward_subs                     full
% 11.02/1.98  --res_forward_subs_resolution           true
% 11.02/1.98  --res_backward_subs_resolution          true
% 11.02/1.98  --res_orphan_elimination                true
% 11.02/1.98  --res_time_limit                        2.
% 11.02/1.98  --res_out_proof                         true
% 11.02/1.98  
% 11.02/1.98  ------ Superposition Options
% 11.02/1.98  
% 11.02/1.98  --superposition_flag                    true
% 11.02/1.98  --sup_passive_queue_type                priority_queues
% 11.02/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.02/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.02/1.98  --demod_completeness_check              fast
% 11.02/1.98  --demod_use_ground                      true
% 11.02/1.98  --sup_to_prop_solver                    passive
% 11.02/1.98  --sup_prop_simpl_new                    true
% 11.02/1.98  --sup_prop_simpl_given                  true
% 11.02/1.98  --sup_fun_splitting                     true
% 11.02/1.98  --sup_smt_interval                      50000
% 11.02/1.98  
% 11.02/1.98  ------ Superposition Simplification Setup
% 11.02/1.98  
% 11.02/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.02/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.02/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.02/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.02/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.02/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.02/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.02/1.98  --sup_immed_triv                        [TrivRules]
% 11.02/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.02/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.02/1.98  --sup_immed_bw_main                     []
% 11.02/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.02/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.02/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.02/1.98  --sup_input_bw                          []
% 11.02/1.98  
% 11.02/1.98  ------ Combination Options
% 11.02/1.98  
% 11.02/1.98  --comb_res_mult                         3
% 11.02/1.98  --comb_sup_mult                         2
% 11.02/1.98  --comb_inst_mult                        10
% 11.02/1.98  
% 11.02/1.98  ------ Debug Options
% 11.02/1.98  
% 11.02/1.98  --dbg_backtrace                         false
% 11.02/1.98  --dbg_dump_prop_clauses                 false
% 11.02/1.98  --dbg_dump_prop_clauses_file            -
% 11.02/1.98  --dbg_out_stat                          false
% 11.02/1.98  ------ Parsing...
% 11.02/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.02/1.98  
% 11.02/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 11.02/1.98  
% 11.02/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.02/1.98  
% 11.02/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.02/1.98  ------ Proving...
% 11.02/1.98  ------ Problem Properties 
% 11.02/1.98  
% 11.02/1.98  
% 11.02/1.98  clauses                                 23
% 11.02/1.98  conjectures                             2
% 11.02/1.98  EPR                                     8
% 11.02/1.98  Horn                                    18
% 11.02/1.98  unary                                   8
% 11.02/1.98  binary                                  7
% 11.02/1.98  lits                                    50
% 11.02/1.98  lits eq                                 8
% 11.02/1.98  fd_pure                                 0
% 11.02/1.98  fd_pseudo                               0
% 11.02/1.98  fd_cond                                 0
% 11.02/1.98  fd_pseudo_cond                          3
% 11.02/1.98  AC symbols                              0
% 11.02/1.98  
% 11.02/1.98  ------ Schedule dynamic 5 is on 
% 11.02/1.98  
% 11.02/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.02/1.98  
% 11.02/1.98  
% 11.02/1.98  ------ 
% 11.02/1.98  Current options:
% 11.02/1.98  ------ 
% 11.02/1.98  
% 11.02/1.98  ------ Input Options
% 11.02/1.98  
% 11.02/1.98  --out_options                           all
% 11.02/1.98  --tptp_safe_out                         true
% 11.02/1.98  --problem_path                          ""
% 11.02/1.98  --include_path                          ""
% 11.02/1.98  --clausifier                            res/vclausify_rel
% 11.02/1.98  --clausifier_options                    ""
% 11.02/1.98  --stdin                                 false
% 11.02/1.98  --stats_out                             all
% 11.02/1.98  
% 11.02/1.98  ------ General Options
% 11.02/1.98  
% 11.02/1.98  --fof                                   false
% 11.02/1.98  --time_out_real                         305.
% 11.02/1.98  --time_out_virtual                      -1.
% 11.02/1.98  --symbol_type_check                     false
% 11.02/1.98  --clausify_out                          false
% 11.02/1.98  --sig_cnt_out                           false
% 11.02/1.98  --trig_cnt_out                          false
% 11.02/1.98  --trig_cnt_out_tolerance                1.
% 11.02/1.98  --trig_cnt_out_sk_spl                   false
% 11.02/1.98  --abstr_cl_out                          false
% 11.02/1.98  
% 11.02/1.98  ------ Global Options
% 11.02/1.98  
% 11.02/1.98  --schedule                              default
% 11.02/1.98  --add_important_lit                     false
% 11.02/1.98  --prop_solver_per_cl                    1000
% 11.02/1.98  --min_unsat_core                        false
% 11.02/1.98  --soft_assumptions                      false
% 11.02/1.98  --soft_lemma_size                       3
% 11.02/1.98  --prop_impl_unit_size                   0
% 11.02/1.98  --prop_impl_unit                        []
% 11.02/1.98  --share_sel_clauses                     true
% 11.02/1.98  --reset_solvers                         false
% 11.02/1.98  --bc_imp_inh                            [conj_cone]
% 11.02/1.98  --conj_cone_tolerance                   3.
% 11.02/1.98  --extra_neg_conj                        none
% 11.02/1.98  --large_theory_mode                     true
% 11.02/1.98  --prolific_symb_bound                   200
% 11.02/1.98  --lt_threshold                          2000
% 11.02/1.98  --clause_weak_htbl                      true
% 11.02/1.98  --gc_record_bc_elim                     false
% 11.02/1.98  
% 11.02/1.98  ------ Preprocessing Options
% 11.02/1.98  
% 11.02/1.98  --preprocessing_flag                    true
% 11.02/1.98  --time_out_prep_mult                    0.1
% 11.02/1.98  --splitting_mode                        input
% 11.02/1.98  --splitting_grd                         true
% 11.02/1.98  --splitting_cvd                         false
% 11.02/1.98  --splitting_cvd_svl                     false
% 11.02/1.98  --splitting_nvd                         32
% 11.02/1.98  --sub_typing                            true
% 11.02/1.98  --prep_gs_sim                           true
% 11.02/1.98  --prep_unflatten                        true
% 11.02/1.98  --prep_res_sim                          true
% 11.02/1.98  --prep_upred                            true
% 11.02/1.98  --prep_sem_filter                       exhaustive
% 11.02/1.98  --prep_sem_filter_out                   false
% 11.02/1.98  --pred_elim                             true
% 11.02/1.98  --res_sim_input                         true
% 11.02/1.98  --eq_ax_congr_red                       true
% 11.02/1.98  --pure_diseq_elim                       true
% 11.02/1.98  --brand_transform                       false
% 11.02/1.98  --non_eq_to_eq                          false
% 11.02/1.98  --prep_def_merge                        true
% 11.02/1.98  --prep_def_merge_prop_impl              false
% 11.02/1.98  --prep_def_merge_mbd                    true
% 11.02/1.98  --prep_def_merge_tr_red                 false
% 11.02/1.98  --prep_def_merge_tr_cl                  false
% 11.02/1.98  --smt_preprocessing                     true
% 11.02/1.98  --smt_ac_axioms                         fast
% 11.02/1.98  --preprocessed_out                      false
% 11.02/1.98  --preprocessed_stats                    false
% 11.02/1.98  
% 11.02/1.98  ------ Abstraction refinement Options
% 11.02/1.98  
% 11.02/1.98  --abstr_ref                             []
% 11.02/1.98  --abstr_ref_prep                        false
% 11.02/1.98  --abstr_ref_until_sat                   false
% 11.02/1.98  --abstr_ref_sig_restrict                funpre
% 11.02/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.02/1.98  --abstr_ref_under                       []
% 11.02/1.98  
% 11.02/1.98  ------ SAT Options
% 11.02/1.98  
% 11.02/1.98  --sat_mode                              false
% 11.02/1.98  --sat_fm_restart_options                ""
% 11.02/1.98  --sat_gr_def                            false
% 11.02/1.98  --sat_epr_types                         true
% 11.02/1.98  --sat_non_cyclic_types                  false
% 11.02/1.98  --sat_finite_models                     false
% 11.02/1.98  --sat_fm_lemmas                         false
% 11.02/1.98  --sat_fm_prep                           false
% 11.02/1.98  --sat_fm_uc_incr                        true
% 11.02/1.98  --sat_out_model                         small
% 11.02/1.98  --sat_out_clauses                       false
% 11.02/1.98  
% 11.02/1.98  ------ QBF Options
% 11.02/1.98  
% 11.02/1.98  --qbf_mode                              false
% 11.02/1.98  --qbf_elim_univ                         false
% 11.02/1.98  --qbf_dom_inst                          none
% 11.02/1.98  --qbf_dom_pre_inst                      false
% 11.02/1.98  --qbf_sk_in                             false
% 11.02/1.98  --qbf_pred_elim                         true
% 11.02/1.98  --qbf_split                             512
% 11.02/1.98  
% 11.02/1.98  ------ BMC1 Options
% 11.02/1.98  
% 11.02/1.98  --bmc1_incremental                      false
% 11.02/1.98  --bmc1_axioms                           reachable_all
% 11.02/1.98  --bmc1_min_bound                        0
% 11.02/1.98  --bmc1_max_bound                        -1
% 11.02/1.98  --bmc1_max_bound_default                -1
% 11.02/1.98  --bmc1_symbol_reachability              true
% 11.02/1.98  --bmc1_property_lemmas                  false
% 11.02/1.98  --bmc1_k_induction                      false
% 11.02/1.98  --bmc1_non_equiv_states                 false
% 11.02/1.98  --bmc1_deadlock                         false
% 11.02/1.98  --bmc1_ucm                              false
% 11.02/1.98  --bmc1_add_unsat_core                   none
% 11.02/1.98  --bmc1_unsat_core_children              false
% 11.02/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.02/1.98  --bmc1_out_stat                         full
% 11.02/1.98  --bmc1_ground_init                      false
% 11.02/1.98  --bmc1_pre_inst_next_state              false
% 11.02/1.98  --bmc1_pre_inst_state                   false
% 11.02/1.98  --bmc1_pre_inst_reach_state             false
% 11.02/1.98  --bmc1_out_unsat_core                   false
% 11.02/1.98  --bmc1_aig_witness_out                  false
% 11.02/1.98  --bmc1_verbose                          false
% 11.02/1.98  --bmc1_dump_clauses_tptp                false
% 11.02/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.02/1.98  --bmc1_dump_file                        -
% 11.02/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.02/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.02/1.98  --bmc1_ucm_extend_mode                  1
% 11.02/1.98  --bmc1_ucm_init_mode                    2
% 11.02/1.98  --bmc1_ucm_cone_mode                    none
% 11.02/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.02/1.98  --bmc1_ucm_relax_model                  4
% 11.02/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.02/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.02/1.98  --bmc1_ucm_layered_model                none
% 11.02/1.98  --bmc1_ucm_max_lemma_size               10
% 11.02/1.98  
% 11.02/1.98  ------ AIG Options
% 11.02/1.98  
% 11.02/1.98  --aig_mode                              false
% 11.02/1.98  
% 11.02/1.98  ------ Instantiation Options
% 11.02/1.98  
% 11.02/1.98  --instantiation_flag                    true
% 11.02/1.98  --inst_sos_flag                         true
% 11.02/1.98  --inst_sos_phase                        true
% 11.02/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.02/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.02/1.98  --inst_lit_sel_side                     none
% 11.02/1.98  --inst_solver_per_active                1400
% 11.02/1.98  --inst_solver_calls_frac                1.
% 11.02/1.98  --inst_passive_queue_type               priority_queues
% 11.02/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.02/1.98  --inst_passive_queues_freq              [25;2]
% 11.02/1.98  --inst_dismatching                      true
% 11.02/1.98  --inst_eager_unprocessed_to_passive     true
% 11.02/1.98  --inst_prop_sim_given                   true
% 11.02/1.98  --inst_prop_sim_new                     false
% 11.02/1.98  --inst_subs_new                         false
% 11.02/1.98  --inst_eq_res_simp                      false
% 11.02/1.98  --inst_subs_given                       false
% 11.02/1.98  --inst_orphan_elimination               true
% 11.02/1.98  --inst_learning_loop_flag               true
% 11.02/1.98  --inst_learning_start                   3000
% 11.02/1.98  --inst_learning_factor                  2
% 11.02/1.98  --inst_start_prop_sim_after_learn       3
% 11.02/1.98  --inst_sel_renew                        solver
% 11.02/1.98  --inst_lit_activity_flag                true
% 11.02/1.98  --inst_restr_to_given                   false
% 11.02/1.98  --inst_activity_threshold               500
% 11.02/1.98  --inst_out_proof                        true
% 11.02/1.98  
% 11.02/1.98  ------ Resolution Options
% 11.02/1.98  
% 11.02/1.98  --resolution_flag                       false
% 11.02/1.98  --res_lit_sel                           adaptive
% 11.02/1.98  --res_lit_sel_side                      none
% 11.02/1.98  --res_ordering                          kbo
% 11.02/1.98  --res_to_prop_solver                    active
% 11.02/1.98  --res_prop_simpl_new                    false
% 11.02/1.98  --res_prop_simpl_given                  true
% 11.02/1.98  --res_passive_queue_type                priority_queues
% 11.02/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.02/1.98  --res_passive_queues_freq               [15;5]
% 11.02/1.98  --res_forward_subs                      full
% 11.02/1.98  --res_backward_subs                     full
% 11.02/1.98  --res_forward_subs_resolution           true
% 11.02/1.98  --res_backward_subs_resolution          true
% 11.02/1.98  --res_orphan_elimination                true
% 11.02/1.98  --res_time_limit                        2.
% 11.02/1.98  --res_out_proof                         true
% 11.02/1.98  
% 11.02/1.98  ------ Superposition Options
% 11.02/1.98  
% 11.02/1.98  --superposition_flag                    true
% 11.02/1.98  --sup_passive_queue_type                priority_queues
% 11.02/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.02/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.02/1.98  --demod_completeness_check              fast
% 11.02/1.98  --demod_use_ground                      true
% 11.02/1.98  --sup_to_prop_solver                    passive
% 11.02/1.98  --sup_prop_simpl_new                    true
% 11.02/1.98  --sup_prop_simpl_given                  true
% 11.02/1.98  --sup_fun_splitting                     true
% 11.02/1.98  --sup_smt_interval                      50000
% 11.02/1.98  
% 11.02/1.98  ------ Superposition Simplification Setup
% 11.02/1.98  
% 11.02/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.02/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.02/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.02/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.02/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.02/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.02/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.02/1.98  --sup_immed_triv                        [TrivRules]
% 11.02/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.02/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.02/1.98  --sup_immed_bw_main                     []
% 11.02/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.02/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.02/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.02/1.98  --sup_input_bw                          []
% 11.02/1.98  
% 11.02/1.98  ------ Combination Options
% 11.02/1.98  
% 11.02/1.98  --comb_res_mult                         3
% 11.02/1.98  --comb_sup_mult                         2
% 11.02/1.98  --comb_inst_mult                        10
% 11.02/1.98  
% 11.02/1.98  ------ Debug Options
% 11.02/1.98  
% 11.02/1.98  --dbg_backtrace                         false
% 11.02/1.98  --dbg_dump_prop_clauses                 false
% 11.02/1.98  --dbg_dump_prop_clauses_file            -
% 11.02/1.98  --dbg_out_stat                          false
% 11.02/1.98  
% 11.02/1.98  
% 11.02/1.98  
% 11.02/1.98  
% 11.02/1.98  ------ Proving...
% 11.02/1.98  
% 11.02/1.98  
% 11.02/1.98  % SZS status Theorem for theBenchmark.p
% 11.02/1.98  
% 11.02/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.02/1.98  
% 11.02/1.98  fof(f2,axiom,(
% 11.02/1.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.02/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.02/1.98  
% 11.02/1.98  fof(f12,plain,(
% 11.02/1.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.02/1.98    inference(rectify,[],[f2])).
% 11.02/1.98  
% 11.02/1.98  fof(f15,plain,(
% 11.02/1.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 11.02/1.98    inference(ennf_transformation,[],[f12])).
% 11.02/1.98  
% 11.02/1.98  fof(f34,plain,(
% 11.02/1.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 11.02/1.98    introduced(choice_axiom,[])).
% 11.02/1.98  
% 11.02/1.98  fof(f35,plain,(
% 11.02/1.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 11.02/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f34])).
% 11.02/1.98  
% 11.02/1.98  fof(f56,plain,(
% 11.02/1.98    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 11.02/1.98    inference(cnf_transformation,[],[f35])).
% 11.02/1.98  
% 11.02/1.98  fof(f3,axiom,(
% 11.02/1.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.02/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.02/1.98  
% 11.02/1.98  fof(f16,plain,(
% 11.02/1.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.02/1.98    inference(ennf_transformation,[],[f3])).
% 11.02/1.98  
% 11.02/1.98  fof(f59,plain,(
% 11.02/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.02/1.98    inference(cnf_transformation,[],[f16])).
% 11.02/1.98  
% 11.02/1.98  fof(f26,plain,(
% 11.02/1.98    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 11.02/1.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 11.02/1.98  
% 11.02/1.98  fof(f37,plain,(
% 11.02/1.98    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 11.02/1.98    inference(nnf_transformation,[],[f26])).
% 11.02/1.98  
% 11.02/1.98  fof(f38,plain,(
% 11.02/1.98    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 11.02/1.98    inference(flattening,[],[f37])).
% 11.02/1.98  
% 11.02/1.98  fof(f39,plain,(
% 11.02/1.98    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 11.02/1.98    inference(rectify,[],[f38])).
% 11.02/1.98  
% 11.02/1.98  fof(f42,plain,(
% 11.02/1.98    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 11.02/1.98    introduced(choice_axiom,[])).
% 11.02/1.98  
% 11.02/1.98  fof(f41,plain,(
% 11.02/1.98    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK5(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 11.02/1.98    introduced(choice_axiom,[])).
% 11.02/1.98  
% 11.02/1.98  fof(f40,plain,(
% 11.02/1.98    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK4(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK4(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK4(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.02/1.98    introduced(choice_axiom,[])).
% 11.02/1.98  
% 11.02/1.98  fof(f43,plain,(
% 11.02/1.98    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK4(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0)) = sK4(X0,X1) & r2_hidden(sK5(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK4(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 11.02/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f42,f41,f40])).
% 11.02/1.98  
% 11.02/1.98  fof(f63,plain,(
% 11.02/1.98    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 11.02/1.98    inference(cnf_transformation,[],[f43])).
% 11.02/1.98  
% 11.02/1.98  fof(f7,axiom,(
% 11.02/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 11.02/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.02/1.98  
% 11.02/1.98  fof(f20,plain,(
% 11.02/1.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.02/1.98    inference(ennf_transformation,[],[f7])).
% 11.02/1.98  
% 11.02/1.98  fof(f75,plain,(
% 11.02/1.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.02/1.98    inference(cnf_transformation,[],[f20])).
% 11.02/1.98  
% 11.02/1.98  fof(f10,conjecture,(
% 11.02/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 11.02/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.02/1.98  
% 11.02/1.98  fof(f11,negated_conjecture,(
% 11.02/1.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 11.02/1.98    inference(negated_conjecture,[],[f10])).
% 11.02/1.98  
% 11.02/1.98  fof(f13,plain,(
% 11.02/1.98    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 11.02/1.98    inference(pure_predicate_removal,[],[f11])).
% 11.02/1.98  
% 11.02/1.98  fof(f14,plain,(
% 11.02/1.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 11.02/1.98    inference(pure_predicate_removal,[],[f13])).
% 11.02/1.98  
% 11.02/1.98  fof(f24,plain,(
% 11.02/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 11.02/1.98    inference(ennf_transformation,[],[f14])).
% 11.02/1.98  
% 11.02/1.98  fof(f25,plain,(
% 11.02/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 11.02/1.98    inference(flattening,[],[f24])).
% 11.02/1.98  
% 11.02/1.98  fof(f48,plain,(
% 11.02/1.98    ( ! [X2,X0,X1] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) => ((r1_tsep_1(sK10,X2) | r1_tsep_1(X2,sK10)) & (~r1_tsep_1(sK10,X1) | ~r1_tsep_1(X1,sK10)) & m1_pre_topc(X1,X2) & m1_pre_topc(sK10,X0))) )),
% 11.02/1.98    introduced(choice_axiom,[])).
% 11.02/1.98  
% 11.02/1.98  fof(f47,plain,(
% 11.02/1.98    ( ! [X0,X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) => (? [X3] : ((r1_tsep_1(X3,sK9) | r1_tsep_1(sK9,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,sK9) & m1_pre_topc(X3,X0)) & m1_pre_topc(sK9,X0))) )),
% 11.02/1.98    introduced(choice_axiom,[])).
% 11.02/1.98  
% 11.02/1.98  fof(f46,plain,(
% 11.02/1.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) => (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK8) | ~r1_tsep_1(sK8,X3)) & m1_pre_topc(sK8,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(sK8,X0))) )),
% 11.02/1.98    introduced(choice_axiom,[])).
% 11.02/1.98  
% 11.02/1.98  fof(f45,plain,(
% 11.02/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK7)) & m1_pre_topc(X2,sK7)) & m1_pre_topc(X1,sK7)) & l1_pre_topc(sK7))),
% 11.02/1.98    introduced(choice_axiom,[])).
% 11.02/1.98  
% 11.02/1.98  fof(f49,plain,(
% 11.02/1.98    ((((r1_tsep_1(sK10,sK9) | r1_tsep_1(sK9,sK10)) & (~r1_tsep_1(sK10,sK8) | ~r1_tsep_1(sK8,sK10)) & m1_pre_topc(sK8,sK9) & m1_pre_topc(sK10,sK7)) & m1_pre_topc(sK9,sK7)) & m1_pre_topc(sK8,sK7)) & l1_pre_topc(sK7)),
% 11.02/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f25,f48,f47,f46,f45])).
% 11.02/1.98  
% 11.02/1.98  fof(f81,plain,(
% 11.02/1.98    m1_pre_topc(sK9,sK7)),
% 11.02/1.98    inference(cnf_transformation,[],[f49])).
% 11.02/1.98  
% 11.02/1.98  fof(f79,plain,(
% 11.02/1.98    l1_pre_topc(sK7)),
% 11.02/1.98    inference(cnf_transformation,[],[f49])).
% 11.02/1.98  
% 11.02/1.98  fof(f5,axiom,(
% 11.02/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 11.02/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.02/1.98  
% 11.02/1.98  fof(f18,plain,(
% 11.02/1.98    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 11.02/1.98    inference(ennf_transformation,[],[f5])).
% 11.02/1.98  
% 11.02/1.98  fof(f27,plain,(
% 11.02/1.98    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 11.02/1.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 11.02/1.98  
% 11.02/1.98  fof(f28,plain,(
% 11.02/1.98    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 11.02/1.98    inference(definition_folding,[],[f18,f27,f26])).
% 11.02/1.98  
% 11.02/1.98  fof(f73,plain,(
% 11.02/1.98    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 11.02/1.98    inference(cnf_transformation,[],[f28])).
% 11.02/1.98  
% 11.02/1.98  fof(f36,plain,(
% 11.02/1.98    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 11.02/1.98    inference(nnf_transformation,[],[f27])).
% 11.02/1.98  
% 11.02/1.98  fof(f61,plain,(
% 11.02/1.98    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 11.02/1.98    inference(cnf_transformation,[],[f36])).
% 11.02/1.98  
% 11.02/1.98  fof(f83,plain,(
% 11.02/1.98    m1_pre_topc(sK8,sK9)),
% 11.02/1.98    inference(cnf_transformation,[],[f49])).
% 11.02/1.98  
% 11.02/1.98  fof(f1,axiom,(
% 11.02/1.98    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.02/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.02/1.98  
% 11.02/1.98  fof(f29,plain,(
% 11.02/1.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.02/1.98    inference(nnf_transformation,[],[f1])).
% 11.02/1.98  
% 11.02/1.98  fof(f30,plain,(
% 11.02/1.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.02/1.98    inference(flattening,[],[f29])).
% 11.02/1.98  
% 11.02/1.98  fof(f31,plain,(
% 11.02/1.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.02/1.98    inference(rectify,[],[f30])).
% 11.02/1.98  
% 11.02/1.98  fof(f32,plain,(
% 11.02/1.98    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 11.02/1.98    introduced(choice_axiom,[])).
% 11.02/1.98  
% 11.02/1.98  fof(f33,plain,(
% 11.02/1.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.02/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 11.02/1.98  
% 11.02/1.98  fof(f51,plain,(
% 11.02/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 11.02/1.98    inference(cnf_transformation,[],[f33])).
% 11.02/1.98  
% 11.02/1.98  fof(f87,plain,(
% 11.02/1.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 11.02/1.98    inference(equality_resolution,[],[f51])).
% 11.02/1.98  
% 11.02/1.98  fof(f57,plain,(
% 11.02/1.98    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 11.02/1.98    inference(cnf_transformation,[],[f35])).
% 11.02/1.98  
% 11.02/1.98  fof(f6,axiom,(
% 11.02/1.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 11.02/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.02/1.98  
% 11.02/1.98  fof(f19,plain,(
% 11.02/1.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 11.02/1.98    inference(ennf_transformation,[],[f6])).
% 11.02/1.98  
% 11.02/1.98  fof(f74,plain,(
% 11.02/1.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 11.02/1.98    inference(cnf_transformation,[],[f19])).
% 11.02/1.98  
% 11.02/1.98  fof(f4,axiom,(
% 11.02/1.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 11.02/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.02/1.98  
% 11.02/1.98  fof(f17,plain,(
% 11.02/1.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 11.02/1.98    inference(ennf_transformation,[],[f4])).
% 11.02/1.98  
% 11.02/1.98  fof(f60,plain,(
% 11.02/1.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 11.02/1.98    inference(cnf_transformation,[],[f17])).
% 11.02/1.98  
% 11.02/1.98  fof(f8,axiom,(
% 11.02/1.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 11.02/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.02/1.98  
% 11.02/1.98  fof(f21,plain,(
% 11.02/1.98    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 11.02/1.98    inference(ennf_transformation,[],[f8])).
% 11.02/1.98  
% 11.02/1.98  fof(f44,plain,(
% 11.02/1.98    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 11.02/1.98    inference(nnf_transformation,[],[f21])).
% 11.02/1.98  
% 11.02/1.98  fof(f76,plain,(
% 11.02/1.98    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 11.02/1.98    inference(cnf_transformation,[],[f44])).
% 11.02/1.98  
% 11.02/1.98  fof(f58,plain,(
% 11.02/1.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 11.02/1.98    inference(cnf_transformation,[],[f35])).
% 11.02/1.98  
% 11.02/1.98  fof(f85,plain,(
% 11.02/1.98    r1_tsep_1(sK10,sK9) | r1_tsep_1(sK9,sK10)),
% 11.02/1.98    inference(cnf_transformation,[],[f49])).
% 11.02/1.98  
% 11.02/1.98  fof(f9,axiom,(
% 11.02/1.98    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 11.02/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.02/1.98  
% 11.02/1.98  fof(f22,plain,(
% 11.02/1.98    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 11.02/1.98    inference(ennf_transformation,[],[f9])).
% 11.02/1.98  
% 11.02/1.98  fof(f23,plain,(
% 11.02/1.98    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 11.02/1.98    inference(flattening,[],[f22])).
% 11.02/1.98  
% 11.02/1.98  fof(f78,plain,(
% 11.02/1.98    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 11.02/1.98    inference(cnf_transformation,[],[f23])).
% 11.02/1.98  
% 11.02/1.98  fof(f82,plain,(
% 11.02/1.98    m1_pre_topc(sK10,sK7)),
% 11.02/1.98    inference(cnf_transformation,[],[f49])).
% 11.02/1.98  
% 11.02/1.98  fof(f84,plain,(
% 11.02/1.98    ~r1_tsep_1(sK10,sK8) | ~r1_tsep_1(sK8,sK10)),
% 11.02/1.98    inference(cnf_transformation,[],[f49])).
% 11.02/1.98  
% 11.02/1.98  fof(f77,plain,(
% 11.02/1.98    ( ! [X0,X1] : (r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 11.02/1.98    inference(cnf_transformation,[],[f44])).
% 11.02/1.98  
% 11.02/1.98  cnf(c_8,plain,
% 11.02/1.98      ( r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X0) ),
% 11.02/1.98      inference(cnf_transformation,[],[f56]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1602,plain,
% 11.02/1.98      ( r1_xboole_0(X0,X1) = iProver_top
% 11.02/1.98      | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
% 11.02/1.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_9,plain,
% 11.02/1.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 11.02/1.98      inference(cnf_transformation,[],[f59]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_22,plain,
% 11.02/1.98      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 11.02/1.98      inference(cnf_transformation,[],[f63]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_442,plain,
% 11.02/1.98      ( ~ sP0(X0,X1)
% 11.02/1.98      | k3_xboole_0(X2,X3) = X2
% 11.02/1.98      | k2_struct_0(X1) != X3
% 11.02/1.98      | k2_struct_0(X0) != X2 ),
% 11.02/1.98      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_443,plain,
% 11.02/1.98      ( ~ sP0(X0,X1)
% 11.02/1.98      | k3_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X0) ),
% 11.02/1.98      inference(unflattening,[status(thm)],[c_442]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_25,plain,
% 11.02/1.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 11.02/1.98      inference(cnf_transformation,[],[f75]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_33,negated_conjecture,
% 11.02/1.98      ( m1_pre_topc(sK9,sK7) ),
% 11.02/1.98      inference(cnf_transformation,[],[f81]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_649,plain,
% 11.02/1.98      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK7 != X0 | sK9 != X1 ),
% 11.02/1.98      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_650,plain,
% 11.02/1.98      ( ~ l1_pre_topc(sK7) | l1_pre_topc(sK9) ),
% 11.02/1.98      inference(unflattening,[status(thm)],[c_649]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_35,negated_conjecture,
% 11.02/1.98      ( l1_pre_topc(sK7) ),
% 11.02/1.98      inference(cnf_transformation,[],[f79]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_652,plain,
% 11.02/1.98      ( l1_pre_topc(sK9) ),
% 11.02/1.98      inference(global_propositional_subsumption,
% 11.02/1.98                [status(thm)],
% 11.02/1.98                [c_650,c_35]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_23,plain,
% 11.02/1.98      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 11.02/1.98      inference(cnf_transformation,[],[f73]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_12,plain,
% 11.02/1.98      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 11.02/1.98      inference(cnf_transformation,[],[f61]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_394,plain,
% 11.02/1.98      ( sP0(X0,X1)
% 11.02/1.98      | ~ m1_pre_topc(X0,X1)
% 11.02/1.98      | ~ l1_pre_topc(X1)
% 11.02/1.98      | ~ l1_pre_topc(X0) ),
% 11.02/1.98      inference(resolution,[status(thm)],[c_23,c_12]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_398,plain,
% 11.02/1.98      ( ~ l1_pre_topc(X1) | ~ m1_pre_topc(X0,X1) | sP0(X0,X1) ),
% 11.02/1.98      inference(global_propositional_subsumption,
% 11.02/1.98                [status(thm)],
% 11.02/1.98                [c_394,c_25]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_399,plain,
% 11.02/1.98      ( sP0(X0,X1) | ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) ),
% 11.02/1.98      inference(renaming,[status(thm)],[c_398]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_31,negated_conjecture,
% 11.02/1.98      ( m1_pre_topc(sK8,sK9) ),
% 11.02/1.98      inference(cnf_transformation,[],[f83]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_596,plain,
% 11.02/1.98      ( sP0(X0,X1) | ~ l1_pre_topc(X1) | sK8 != X0 | sK9 != X1 ),
% 11.02/1.98      inference(resolution_lifted,[status(thm)],[c_399,c_31]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_597,plain,
% 11.02/1.98      ( sP0(sK8,sK9) | ~ l1_pre_topc(sK9) ),
% 11.02/1.98      inference(unflattening,[status(thm)],[c_596]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_659,plain,
% 11.02/1.98      ( sP0(sK8,sK9) ),
% 11.02/1.98      inference(backward_subsumption_resolution,
% 11.02/1.98                [status(thm)],
% 11.02/1.98                [c_652,c_597]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_916,plain,
% 11.02/1.98      ( k3_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X0)
% 11.02/1.98      | sK8 != X0
% 11.02/1.98      | sK9 != X1 ),
% 11.02/1.98      inference(resolution_lifted,[status(thm)],[c_443,c_659]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_917,plain,
% 11.02/1.98      ( k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) = k2_struct_0(sK8) ),
% 11.02/1.98      inference(unflattening,[status(thm)],[c_916]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_4,plain,
% 11.02/1.98      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 11.02/1.98      inference(cnf_transformation,[],[f87]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1606,plain,
% 11.02/1.98      ( r2_hidden(X0,X1) = iProver_top
% 11.02/1.98      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 11.02/1.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_2533,plain,
% 11.02/1.98      ( r2_hidden(X0,k2_struct_0(sK8)) != iProver_top
% 11.02/1.98      | r2_hidden(X0,k2_struct_0(sK9)) = iProver_top ),
% 11.02/1.98      inference(superposition,[status(thm)],[c_917,c_1606]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_2996,plain,
% 11.02/1.98      ( r1_xboole_0(k2_struct_0(sK8),X0) = iProver_top
% 11.02/1.98      | r2_hidden(sK3(k2_struct_0(sK8),X0),k2_struct_0(sK9)) = iProver_top ),
% 11.02/1.98      inference(superposition,[status(thm)],[c_1602,c_2533]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_7,plain,
% 11.02/1.98      ( r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X1) ),
% 11.02/1.98      inference(cnf_transformation,[],[f57]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1603,plain,
% 11.02/1.98      ( r1_xboole_0(X0,X1) = iProver_top
% 11.02/1.98      | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
% 11.02/1.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_24,plain,
% 11.02/1.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 11.02/1.98      inference(cnf_transformation,[],[f74]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_705,plain,
% 11.02/1.98      ( l1_struct_0(X0) | sK9 != X0 ),
% 11.02/1.98      inference(resolution_lifted,[status(thm)],[c_24,c_652]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_706,plain,
% 11.02/1.98      ( l1_struct_0(sK9) ),
% 11.02/1.98      inference(unflattening,[status(thm)],[c_705]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1593,plain,
% 11.02/1.98      ( l1_struct_0(sK9) = iProver_top ),
% 11.02/1.98      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_10,plain,
% 11.02/1.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 11.02/1.98      inference(cnf_transformation,[],[f60]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1601,plain,
% 11.02/1.98      ( u1_struct_0(X0) = k2_struct_0(X0)
% 11.02/1.98      | l1_struct_0(X0) != iProver_top ),
% 11.02/1.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_2012,plain,
% 11.02/1.98      ( u1_struct_0(sK9) = k2_struct_0(sK9) ),
% 11.02/1.98      inference(superposition,[status(thm)],[c_1593,c_1601]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_27,plain,
% 11.02/1.98      ( ~ r1_tsep_1(X0,X1)
% 11.02/1.98      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 11.02/1.98      | ~ l1_struct_0(X0)
% 11.02/1.98      | ~ l1_struct_0(X1) ),
% 11.02/1.98      inference(cnf_transformation,[],[f76]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1599,plain,
% 11.02/1.98      ( r1_tsep_1(X0,X1) != iProver_top
% 11.02/1.98      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 11.02/1.98      | l1_struct_0(X0) != iProver_top
% 11.02/1.98      | l1_struct_0(X1) != iProver_top ),
% 11.02/1.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_3284,plain,
% 11.02/1.98      ( r1_tsep_1(sK9,X0) != iProver_top
% 11.02/1.98      | r1_xboole_0(k2_struct_0(sK9),u1_struct_0(X0)) = iProver_top
% 11.02/1.98      | l1_struct_0(X0) != iProver_top
% 11.02/1.98      | l1_struct_0(sK9) != iProver_top ),
% 11.02/1.98      inference(superposition,[status(thm)],[c_2012,c_1599]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_707,plain,
% 11.02/1.98      ( l1_struct_0(sK9) = iProver_top ),
% 11.02/1.98      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_17768,plain,
% 11.02/1.98      ( l1_struct_0(X0) != iProver_top
% 11.02/1.98      | r1_xboole_0(k2_struct_0(sK9),u1_struct_0(X0)) = iProver_top
% 11.02/1.98      | r1_tsep_1(sK9,X0) != iProver_top ),
% 11.02/1.98      inference(global_propositional_subsumption,
% 11.02/1.98                [status(thm)],
% 11.02/1.98                [c_3284,c_707]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_17769,plain,
% 11.02/1.98      ( r1_tsep_1(sK9,X0) != iProver_top
% 11.02/1.98      | r1_xboole_0(k2_struct_0(sK9),u1_struct_0(X0)) = iProver_top
% 11.02/1.98      | l1_struct_0(X0) != iProver_top ),
% 11.02/1.98      inference(renaming,[status(thm)],[c_17768]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_6,plain,
% 11.02/1.98      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 11.02/1.98      inference(cnf_transformation,[],[f58]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1604,plain,
% 11.02/1.98      ( r1_xboole_0(X0,X1) != iProver_top
% 11.02/1.98      | r2_hidden(X2,X1) != iProver_top
% 11.02/1.98      | r2_hidden(X2,X0) != iProver_top ),
% 11.02/1.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_17778,plain,
% 11.02/1.98      ( r1_tsep_1(sK9,X0) != iProver_top
% 11.02/1.98      | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
% 11.02/1.98      | r2_hidden(X1,k2_struct_0(sK9)) != iProver_top
% 11.02/1.98      | l1_struct_0(X0) != iProver_top ),
% 11.02/1.98      inference(superposition,[status(thm)],[c_17769,c_1604]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_32743,plain,
% 11.02/1.98      ( r1_tsep_1(sK9,X0) != iProver_top
% 11.02/1.98      | r1_xboole_0(X1,u1_struct_0(X0)) = iProver_top
% 11.02/1.98      | r2_hidden(sK3(X1,u1_struct_0(X0)),k2_struct_0(sK9)) != iProver_top
% 11.02/1.98      | l1_struct_0(X0) != iProver_top ),
% 11.02/1.98      inference(superposition,[status(thm)],[c_1603,c_17778]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_46725,plain,
% 11.02/1.98      ( r1_tsep_1(sK9,X0) != iProver_top
% 11.02/1.98      | r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X0)) = iProver_top
% 11.02/1.98      | l1_struct_0(X0) != iProver_top ),
% 11.02/1.98      inference(superposition,[status(thm)],[c_2996,c_32743]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_46769,plain,
% 11.02/1.98      ( r1_tsep_1(sK9,sK10) != iProver_top
% 11.02/1.98      | r1_xboole_0(k2_struct_0(sK8),u1_struct_0(sK10)) = iProver_top
% 11.02/1.98      | l1_struct_0(sK10) != iProver_top ),
% 11.02/1.98      inference(instantiation,[status(thm)],[c_46725]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_29,negated_conjecture,
% 11.02/1.98      ( r1_tsep_1(sK9,sK10) | r1_tsep_1(sK10,sK9) ),
% 11.02/1.98      inference(cnf_transformation,[],[f85]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1597,plain,
% 11.02/1.98      ( r1_tsep_1(sK9,sK10) = iProver_top
% 11.02/1.98      | r1_tsep_1(sK10,sK9) = iProver_top ),
% 11.02/1.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_28,plain,
% 11.02/1.98      ( ~ r1_tsep_1(X0,X1)
% 11.02/1.98      | r1_tsep_1(X1,X0)
% 11.02/1.98      | ~ l1_struct_0(X0)
% 11.02/1.98      | ~ l1_struct_0(X1) ),
% 11.02/1.98      inference(cnf_transformation,[],[f78]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1598,plain,
% 11.02/1.98      ( r1_tsep_1(X0,X1) != iProver_top
% 11.02/1.98      | r1_tsep_1(X1,X0) = iProver_top
% 11.02/1.98      | l1_struct_0(X0) != iProver_top
% 11.02/1.98      | l1_struct_0(X1) != iProver_top ),
% 11.02/1.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_2644,plain,
% 11.02/1.98      ( r1_tsep_1(sK10,sK9) = iProver_top
% 11.02/1.98      | l1_struct_0(sK9) != iProver_top
% 11.02/1.98      | l1_struct_0(sK10) != iProver_top ),
% 11.02/1.98      inference(superposition,[status(thm)],[c_1597,c_1598]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_36,plain,
% 11.02/1.98      ( l1_pre_topc(sK7) = iProver_top ),
% 11.02/1.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_51,plain,
% 11.02/1.98      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 11.02/1.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_53,plain,
% 11.02/1.98      ( l1_pre_topc(sK10) != iProver_top
% 11.02/1.98      | l1_struct_0(sK10) = iProver_top ),
% 11.02/1.98      inference(instantiation,[status(thm)],[c_51]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_32,negated_conjecture,
% 11.02/1.98      ( m1_pre_topc(sK10,sK7) ),
% 11.02/1.98      inference(cnf_transformation,[],[f82]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_627,plain,
% 11.02/1.98      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK7 != X0 | sK10 != X1 ),
% 11.02/1.98      inference(resolution_lifted,[status(thm)],[c_25,c_32]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_628,plain,
% 11.02/1.98      ( ~ l1_pre_topc(sK7) | l1_pre_topc(sK10) ),
% 11.02/1.98      inference(unflattening,[status(thm)],[c_627]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_629,plain,
% 11.02/1.98      ( l1_pre_topc(sK7) != iProver_top
% 11.02/1.98      | l1_pre_topc(sK10) = iProver_top ),
% 11.02/1.98      inference(predicate_to_equality,[status(thm)],[c_628]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_2907,plain,
% 11.02/1.98      ( r1_tsep_1(sK10,sK9) = iProver_top ),
% 11.02/1.98      inference(global_propositional_subsumption,
% 11.02/1.98                [status(thm)],
% 11.02/1.98                [c_2644,c_36,c_53,c_629,c_707]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_2911,plain,
% 11.02/1.98      ( r1_tsep_1(sK9,sK10) = iProver_top
% 11.02/1.98      | l1_struct_0(sK9) != iProver_top
% 11.02/1.98      | l1_struct_0(sK10) != iProver_top ),
% 11.02/1.98      inference(superposition,[status(thm)],[c_2907,c_1598]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1261,plain,( X0 = X0 ),theory(equality) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_2781,plain,
% 11.02/1.98      ( u1_struct_0(sK10) = u1_struct_0(sK10) ),
% 11.02/1.98      inference(instantiation,[status(thm)],[c_1261]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1265,plain,
% 11.02/1.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.02/1.98      theory(equality) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1662,plain,
% 11.02/1.98      ( ~ r1_xboole_0(X0,X1)
% 11.02/1.98      | r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10))
% 11.02/1.98      | u1_struct_0(sK8) != X0
% 11.02/1.98      | u1_struct_0(sK10) != X1 ),
% 11.02/1.98      inference(instantiation,[status(thm)],[c_1265]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1733,plain,
% 11.02/1.98      ( r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10))
% 11.02/1.98      | ~ r1_xboole_0(k2_struct_0(sK8),X0)
% 11.02/1.98      | u1_struct_0(sK8) != k2_struct_0(sK8)
% 11.02/1.98      | u1_struct_0(sK10) != X0 ),
% 11.02/1.98      inference(instantiation,[status(thm)],[c_1662]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_2089,plain,
% 11.02/1.98      ( r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10))
% 11.02/1.98      | ~ r1_xboole_0(k2_struct_0(sK8),u1_struct_0(sK10))
% 11.02/1.98      | u1_struct_0(sK8) != k2_struct_0(sK8)
% 11.02/1.98      | u1_struct_0(sK10) != u1_struct_0(sK10) ),
% 11.02/1.98      inference(instantiation,[status(thm)],[c_1733]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_2092,plain,
% 11.02/1.98      ( u1_struct_0(sK8) != k2_struct_0(sK8)
% 11.02/1.98      | u1_struct_0(sK10) != u1_struct_0(sK10)
% 11.02/1.98      | r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10)) = iProver_top
% 11.02/1.98      | r1_xboole_0(k2_struct_0(sK8),u1_struct_0(sK10)) != iProver_top ),
% 11.02/1.98      inference(predicate_to_equality,[status(thm)],[c_2089]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1879,plain,
% 11.02/1.98      ( ~ l1_struct_0(sK8) | u1_struct_0(sK8) = k2_struct_0(sK8) ),
% 11.02/1.98      inference(instantiation,[status(thm)],[c_10]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1670,plain,
% 11.02/1.98      ( ~ r1_tsep_1(sK8,sK10)
% 11.02/1.98      | r1_tsep_1(sK10,sK8)
% 11.02/1.98      | ~ l1_struct_0(sK8)
% 11.02/1.98      | ~ l1_struct_0(sK10) ),
% 11.02/1.98      inference(instantiation,[status(thm)],[c_28]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1671,plain,
% 11.02/1.98      ( r1_tsep_1(sK8,sK10) != iProver_top
% 11.02/1.98      | r1_tsep_1(sK10,sK8) = iProver_top
% 11.02/1.98      | l1_struct_0(sK8) != iProver_top
% 11.02/1.98      | l1_struct_0(sK10) != iProver_top ),
% 11.02/1.98      inference(predicate_to_equality,[status(thm)],[c_1670]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_30,negated_conjecture,
% 11.02/1.98      ( ~ r1_tsep_1(sK8,sK10) | ~ r1_tsep_1(sK10,sK8) ),
% 11.02/1.98      inference(cnf_transformation,[],[f84]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1596,plain,
% 11.02/1.98      ( r1_tsep_1(sK8,sK10) != iProver_top
% 11.02/1.98      | r1_tsep_1(sK10,sK8) != iProver_top ),
% 11.02/1.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_41,plain,
% 11.02/1.98      ( r1_tsep_1(sK8,sK10) != iProver_top
% 11.02/1.98      | r1_tsep_1(sK10,sK8) != iProver_top ),
% 11.02/1.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_606,plain,
% 11.02/1.98      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK8 != X1 | sK9 != X0 ),
% 11.02/1.98      inference(resolution_lifted,[status(thm)],[c_25,c_31]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_607,plain,
% 11.02/1.98      ( l1_pre_topc(sK8) | ~ l1_pre_topc(sK9) ),
% 11.02/1.98      inference(unflattening,[status(thm)],[c_606]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_660,plain,
% 11.02/1.98      ( l1_pre_topc(sK8) ),
% 11.02/1.98      inference(backward_subsumption_resolution,
% 11.02/1.98                [status(thm)],
% 11.02/1.98                [c_652,c_607]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_712,plain,
% 11.02/1.98      ( l1_struct_0(X0) | sK8 != X0 ),
% 11.02/1.98      inference(resolution_lifted,[status(thm)],[c_24,c_660]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_713,plain,
% 11.02/1.98      ( l1_struct_0(sK8) ),
% 11.02/1.98      inference(unflattening,[status(thm)],[c_712]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_714,plain,
% 11.02/1.98      ( l1_struct_0(sK8) = iProver_top ),
% 11.02/1.98      inference(predicate_to_equality,[status(thm)],[c_713]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1639,plain,
% 11.02/1.98      ( r1_tsep_1(sK8,sK10)
% 11.02/1.98      | ~ r1_tsep_1(sK10,sK8)
% 11.02/1.98      | ~ l1_struct_0(sK8)
% 11.02/1.98      | ~ l1_struct_0(sK10) ),
% 11.02/1.98      inference(instantiation,[status(thm)],[c_28]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1640,plain,
% 11.02/1.98      ( r1_tsep_1(sK8,sK10) = iProver_top
% 11.02/1.98      | r1_tsep_1(sK10,sK8) != iProver_top
% 11.02/1.98      | l1_struct_0(sK8) != iProver_top
% 11.02/1.98      | l1_struct_0(sK10) != iProver_top ),
% 11.02/1.98      inference(predicate_to_equality,[status(thm)],[c_1639]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1648,plain,
% 11.02/1.98      ( r1_tsep_1(sK10,sK8) != iProver_top ),
% 11.02/1.98      inference(global_propositional_subsumption,
% 11.02/1.98                [status(thm)],
% 11.02/1.98                [c_1596,c_36,c_41,c_53,c_629,c_714,c_1640]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_26,plain,
% 11.02/1.98      ( r1_tsep_1(X0,X1)
% 11.02/1.98      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 11.02/1.98      | ~ l1_struct_0(X0)
% 11.02/1.98      | ~ l1_struct_0(X1) ),
% 11.02/1.98      inference(cnf_transformation,[],[f77]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1636,plain,
% 11.02/1.98      ( r1_tsep_1(sK8,sK10)
% 11.02/1.98      | ~ r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10))
% 11.02/1.98      | ~ l1_struct_0(sK8)
% 11.02/1.98      | ~ l1_struct_0(sK10) ),
% 11.02/1.98      inference(instantiation,[status(thm)],[c_26]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(c_1637,plain,
% 11.02/1.98      ( r1_tsep_1(sK8,sK10) = iProver_top
% 11.02/1.98      | r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10)) != iProver_top
% 11.02/1.98      | l1_struct_0(sK8) != iProver_top
% 11.02/1.98      | l1_struct_0(sK10) != iProver_top ),
% 11.02/1.98      inference(predicate_to_equality,[status(thm)],[c_1636]) ).
% 11.02/1.98  
% 11.02/1.98  cnf(contradiction,plain,
% 11.02/1.98      ( $false ),
% 11.02/1.98      inference(minisat,
% 11.02/1.98                [status(thm)],
% 11.02/1.98                [c_46769,c_2911,c_2781,c_2092,c_1879,c_1671,c_1648,
% 11.02/1.98                 c_1637,c_714,c_713,c_707,c_629,c_53,c_36]) ).
% 11.02/1.98  
% 11.02/1.98  
% 11.02/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.02/1.98  
% 11.02/1.98  ------                               Statistics
% 11.02/1.98  
% 11.02/1.98  ------ General
% 11.02/1.98  
% 11.02/1.98  abstr_ref_over_cycles:                  0
% 11.02/1.98  abstr_ref_under_cycles:                 0
% 11.02/1.98  gc_basic_clause_elim:                   0
% 11.02/1.98  forced_gc_time:                         0
% 11.02/1.98  parsing_time:                           0.017
% 11.02/1.98  unif_index_cands_time:                  0.
% 11.02/1.98  unif_index_add_time:                    0.
% 11.02/1.98  orderings_time:                         0.
% 11.02/1.98  out_proof_time:                         0.012
% 11.02/1.98  total_time:                             1.25
% 11.02/1.98  num_of_symbols:                         56
% 11.02/1.98  num_of_terms:                           47447
% 11.02/1.98  
% 11.02/1.98  ------ Preprocessing
% 11.02/1.98  
% 11.02/1.98  num_of_splits:                          0
% 11.02/1.98  num_of_split_atoms:                     0
% 11.02/1.98  num_of_reused_defs:                     0
% 11.02/1.98  num_eq_ax_congr_red:                    47
% 11.02/1.98  num_of_sem_filtered_clauses:            6
% 11.02/1.98  num_of_subtypes:                        0
% 11.02/1.98  monotx_restored_types:                  0
% 11.02/1.98  sat_num_of_epr_types:                   0
% 11.02/1.98  sat_num_of_non_cyclic_types:            0
% 11.02/1.98  sat_guarded_non_collapsed_types:        0
% 11.02/1.98  num_pure_diseq_elim:                    0
% 11.02/1.98  simp_replaced_by:                       0
% 11.02/1.98  res_preprocessed:                       151
% 11.02/1.98  prep_upred:                             0
% 11.02/1.98  prep_unflattend:                        48
% 11.02/1.98  smt_new_axioms:                         0
% 11.02/1.98  pred_elim_cands:                        4
% 11.02/1.98  pred_elim:                              5
% 11.02/1.98  pred_elim_cl:                           8
% 11.02/1.98  pred_elim_cycles:                       9
% 11.02/1.98  merged_defs:                            0
% 11.02/1.98  merged_defs_ncl:                        0
% 11.02/1.98  bin_hyper_res:                          0
% 11.02/1.98  prep_cycles:                            5
% 11.02/1.98  pred_elim_time:                         0.005
% 11.02/1.98  splitting_time:                         0.
% 11.02/1.98  sem_filter_time:                        0.
% 11.02/1.98  monotx_time:                            0.
% 11.02/1.98  subtype_inf_time:                       0.
% 11.02/1.98  
% 11.02/1.98  ------ Problem properties
% 11.02/1.98  
% 11.02/1.98  clauses:                                23
% 11.02/1.98  conjectures:                            2
% 11.02/1.98  epr:                                    8
% 11.02/1.98  horn:                                   18
% 11.02/1.98  ground:                                 10
% 11.02/1.98  unary:                                  8
% 11.02/1.98  binary:                                 7
% 11.02/1.98  lits:                                   50
% 11.02/1.98  lits_eq:                                8
% 11.02/1.98  fd_pure:                                0
% 11.02/1.98  fd_pseudo:                              0
% 11.02/1.98  fd_cond:                                0
% 11.02/1.98  fd_pseudo_cond:                         3
% 11.02/1.98  ac_symbols:                             0
% 11.02/1.98  
% 11.02/1.98  ------ Propositional Solver
% 11.02/1.98  
% 11.02/1.98  prop_solver_calls:                      40
% 11.02/1.98  prop_fast_solver_calls:                 2353
% 11.02/1.98  smt_solver_calls:                       0
% 11.02/1.98  smt_fast_solver_calls:                  0
% 11.02/1.98  prop_num_of_clauses:                    22459
% 11.02/1.98  prop_preprocess_simplified:             32654
% 11.02/1.98  prop_fo_subsumed:                       138
% 11.02/1.98  prop_solver_time:                       0.
% 11.02/1.98  smt_solver_time:                        0.
% 11.02/1.98  smt_fast_solver_time:                   0.
% 11.02/1.98  prop_fast_solver_time:                  0.
% 11.02/1.98  prop_unsat_core_time:                   0.002
% 11.02/1.98  
% 11.02/1.98  ------ QBF
% 11.02/1.98  
% 11.02/1.98  qbf_q_res:                              0
% 11.02/1.98  qbf_num_tautologies:                    0
% 11.02/1.98  qbf_prep_cycles:                        0
% 11.02/1.98  
% 11.02/1.98  ------ BMC1
% 11.02/1.98  
% 11.02/1.98  bmc1_current_bound:                     -1
% 11.02/1.98  bmc1_last_solved_bound:                 -1
% 11.02/1.98  bmc1_unsat_core_size:                   -1
% 11.02/1.98  bmc1_unsat_core_parents_size:           -1
% 11.02/1.98  bmc1_merge_next_fun:                    0
% 11.02/1.98  bmc1_unsat_core_clauses_time:           0.
% 11.02/1.98  
% 11.02/1.98  ------ Instantiation
% 11.02/1.98  
% 11.02/1.98  inst_num_of_clauses:                    4253
% 11.02/1.98  inst_num_in_passive:                    1191
% 11.02/1.98  inst_num_in_active:                     2045
% 11.02/1.98  inst_num_in_unprocessed:                1017
% 11.02/1.98  inst_num_of_loops:                      2590
% 11.02/1.98  inst_num_of_learning_restarts:          0
% 11.02/1.98  inst_num_moves_active_passive:          540
% 11.02/1.98  inst_lit_activity:                      0
% 11.02/1.98  inst_lit_activity_moves:                1
% 11.02/1.98  inst_num_tautologies:                   0
% 11.02/1.98  inst_num_prop_implied:                  0
% 11.02/1.98  inst_num_existing_simplified:           0
% 11.02/1.98  inst_num_eq_res_simplified:             0
% 11.02/1.98  inst_num_child_elim:                    0
% 11.02/1.98  inst_num_of_dismatching_blockings:      4608
% 11.02/1.98  inst_num_of_non_proper_insts:           5845
% 11.02/1.98  inst_num_of_duplicates:                 0
% 11.02/1.98  inst_inst_num_from_inst_to_res:         0
% 11.02/1.98  inst_dismatching_checking_time:         0.
% 11.02/1.98  
% 11.02/1.98  ------ Resolution
% 11.02/1.98  
% 11.02/1.98  res_num_of_clauses:                     0
% 11.02/1.98  res_num_in_passive:                     0
% 11.02/1.98  res_num_in_active:                      0
% 11.02/1.98  res_num_of_loops:                       156
% 11.02/1.98  res_forward_subset_subsumed:            149
% 11.02/1.98  res_backward_subset_subsumed:           2
% 11.02/1.98  res_forward_subsumed:                   0
% 11.02/1.98  res_backward_subsumed:                  0
% 11.02/1.98  res_forward_subsumption_resolution:     0
% 11.02/1.98  res_backward_subsumption_resolution:    2
% 11.02/1.98  res_clause_to_clause_subsumption:       47669
% 11.02/1.98  res_orphan_elimination:                 0
% 11.02/1.98  res_tautology_del:                      190
% 11.02/1.98  res_num_eq_res_simplified:              0
% 11.02/1.98  res_num_sel_changes:                    0
% 11.02/1.98  res_moves_from_active_to_pass:          0
% 11.02/1.98  
% 11.02/1.98  ------ Superposition
% 11.02/1.98  
% 11.02/1.98  sup_time_total:                         0.
% 11.02/1.98  sup_time_generating:                    0.
% 11.02/1.98  sup_time_sim_full:                      0.
% 11.02/1.98  sup_time_sim_immed:                     0.
% 11.02/1.98  
% 11.02/1.98  sup_num_of_clauses:                     2600
% 11.02/1.98  sup_num_in_active:                      446
% 11.02/1.98  sup_num_in_passive:                     2154
% 11.02/1.98  sup_num_of_loops:                       517
% 11.02/1.98  sup_fw_superposition:                   2963
% 11.02/1.98  sup_bw_superposition:                   2004
% 11.02/1.98  sup_immediate_simplified:               1282
% 11.02/1.98  sup_given_eliminated:                   0
% 11.02/1.98  comparisons_done:                       0
% 11.02/1.98  comparisons_avoided:                    0
% 11.02/1.98  
% 11.02/1.98  ------ Simplifications
% 11.02/1.98  
% 11.02/1.98  
% 11.02/1.98  sim_fw_subset_subsumed:                 130
% 11.02/1.98  sim_bw_subset_subsumed:                 300
% 11.02/1.98  sim_fw_subsumed:                        730
% 11.02/1.98  sim_bw_subsumed:                        61
% 11.02/1.98  sim_fw_subsumption_res:                 0
% 11.02/1.98  sim_bw_subsumption_res:                 0
% 11.02/1.98  sim_tautology_del:                      94
% 11.02/1.98  sim_eq_tautology_del:                   0
% 11.02/1.98  sim_eq_res_simp:                        35
% 11.02/1.98  sim_fw_demodulated:                     0
% 11.02/1.98  sim_bw_demodulated:                     0
% 11.02/1.98  sim_light_normalised:                   726
% 11.02/1.98  sim_joinable_taut:                      0
% 11.02/1.98  sim_joinable_simp:                      0
% 11.02/1.98  sim_ac_normalised:                      0
% 11.02/1.98  sim_smt_subsumption:                    0
% 11.02/1.98  
%------------------------------------------------------------------------------
