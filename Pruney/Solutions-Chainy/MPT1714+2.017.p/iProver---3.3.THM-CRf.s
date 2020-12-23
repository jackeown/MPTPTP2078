%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:59 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_442,plain,
    ( ~ sP0(X0,X1)
    | k2_xboole_0(X2,X3) = X3
    | k2_struct_0(X1) != X3
    | k2_struct_0(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_443,plain,
    ( ~ sP0(X0,X1)
    | k2_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X1) ),
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
    ( k2_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X1)
    | sK8 != X0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_443,c_659])).

cnf(c_917,plain,
    ( k2_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) = k2_struct_0(sK9) ),
    inference(unflattening,[status(thm)],[c_916])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1606,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2176,plain,
    ( r2_hidden(X0,k2_struct_0(sK8)) != iProver_top
    | r2_hidden(X0,k2_struct_0(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_917,c_1606])).

cnf(c_2596,plain,
    ( r1_xboole_0(k2_struct_0(sK8),X0) = iProver_top
    | r2_hidden(sK3(k2_struct_0(sK8),X0),k2_struct_0(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1602,c_2176])).

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

cnf(c_2008,plain,
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

cnf(c_3202,plain,
    ( r1_tsep_1(sK9,X0) != iProver_top
    | r1_xboole_0(k2_struct_0(sK9),u1_struct_0(X0)) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_2008,c_1599])).

cnf(c_707,plain,
    ( l1_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_5485,plain,
    ( l1_struct_0(X0) != iProver_top
    | r1_xboole_0(k2_struct_0(sK9),u1_struct_0(X0)) = iProver_top
    | r1_tsep_1(sK9,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3202,c_707])).

cnf(c_5486,plain,
    ( r1_tsep_1(sK9,X0) != iProver_top
    | r1_xboole_0(k2_struct_0(sK9),u1_struct_0(X0)) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5485])).

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

cnf(c_5495,plain,
    ( r1_tsep_1(sK9,X0) != iProver_top
    | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X1,k2_struct_0(sK9)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5486,c_1604])).

cnf(c_12421,plain,
    ( r1_tsep_1(sK9,X0) != iProver_top
    | r1_xboole_0(X1,u1_struct_0(X0)) = iProver_top
    | r2_hidden(sK3(X1,u1_struct_0(X0)),k2_struct_0(sK9)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1603,c_5495])).

cnf(c_17529,plain,
    ( r1_tsep_1(sK9,X0) != iProver_top
    | r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X0)) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2596,c_12421])).

cnf(c_17541,plain,
    ( r1_tsep_1(sK9,sK10) != iProver_top
    | r1_xboole_0(k2_struct_0(sK8),u1_struct_0(sK10)) = iProver_top
    | l1_struct_0(sK10) != iProver_top ),
    inference(instantiation,[status(thm)],[c_17529])).

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

cnf(c_2604,plain,
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

cnf(c_2898,plain,
    ( r1_tsep_1(sK10,sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2604,c_36,c_53,c_629,c_707])).

cnf(c_2902,plain,
    ( r1_tsep_1(sK9,sK10) = iProver_top
    | l1_struct_0(sK9) != iProver_top
    | l1_struct_0(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_2898,c_1598])).

cnf(c_1261,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2126,plain,
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

cnf(c_2068,plain,
    ( r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10))
    | ~ r1_xboole_0(k2_struct_0(sK8),u1_struct_0(sK10))
    | u1_struct_0(sK8) != k2_struct_0(sK8)
    | u1_struct_0(sK10) != u1_struct_0(sK10) ),
    inference(instantiation,[status(thm)],[c_1733])).

cnf(c_2071,plain,
    ( u1_struct_0(sK8) != k2_struct_0(sK8)
    | u1_struct_0(sK10) != u1_struct_0(sK10)
    | r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10)) = iProver_top
    | r1_xboole_0(k2_struct_0(sK8),u1_struct_0(sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2068])).

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
    inference(minisat,[status(thm)],[c_17541,c_2902,c_2126,c_2071,c_1879,c_1671,c_1648,c_1637,c_714,c_713,c_707,c_629,c_53,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:03:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.07/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/0.99  
% 4.07/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.07/0.99  
% 4.07/0.99  ------  iProver source info
% 4.07/0.99  
% 4.07/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.07/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.07/0.99  git: non_committed_changes: false
% 4.07/0.99  git: last_make_outside_of_git: false
% 4.07/0.99  
% 4.07/0.99  ------ 
% 4.07/0.99  
% 4.07/0.99  ------ Input Options
% 4.07/0.99  
% 4.07/0.99  --out_options                           all
% 4.07/0.99  --tptp_safe_out                         true
% 4.07/0.99  --problem_path                          ""
% 4.07/0.99  --include_path                          ""
% 4.07/0.99  --clausifier                            res/vclausify_rel
% 4.07/0.99  --clausifier_options                    ""
% 4.07/0.99  --stdin                                 false
% 4.07/0.99  --stats_out                             all
% 4.07/0.99  
% 4.07/0.99  ------ General Options
% 4.07/0.99  
% 4.07/0.99  --fof                                   false
% 4.07/0.99  --time_out_real                         305.
% 4.07/0.99  --time_out_virtual                      -1.
% 4.07/0.99  --symbol_type_check                     false
% 4.07/0.99  --clausify_out                          false
% 4.07/0.99  --sig_cnt_out                           false
% 4.07/0.99  --trig_cnt_out                          false
% 4.07/0.99  --trig_cnt_out_tolerance                1.
% 4.07/0.99  --trig_cnt_out_sk_spl                   false
% 4.07/0.99  --abstr_cl_out                          false
% 4.07/0.99  
% 4.07/0.99  ------ Global Options
% 4.07/0.99  
% 4.07/0.99  --schedule                              default
% 4.07/0.99  --add_important_lit                     false
% 4.07/0.99  --prop_solver_per_cl                    1000
% 4.07/0.99  --min_unsat_core                        false
% 4.07/0.99  --soft_assumptions                      false
% 4.07/0.99  --soft_lemma_size                       3
% 4.07/0.99  --prop_impl_unit_size                   0
% 4.07/0.99  --prop_impl_unit                        []
% 4.07/0.99  --share_sel_clauses                     true
% 4.07/0.99  --reset_solvers                         false
% 4.07/0.99  --bc_imp_inh                            [conj_cone]
% 4.07/0.99  --conj_cone_tolerance                   3.
% 4.07/0.99  --extra_neg_conj                        none
% 4.07/0.99  --large_theory_mode                     true
% 4.07/0.99  --prolific_symb_bound                   200
% 4.07/0.99  --lt_threshold                          2000
% 4.07/0.99  --clause_weak_htbl                      true
% 4.07/0.99  --gc_record_bc_elim                     false
% 4.07/0.99  
% 4.07/0.99  ------ Preprocessing Options
% 4.07/0.99  
% 4.07/0.99  --preprocessing_flag                    true
% 4.07/0.99  --time_out_prep_mult                    0.1
% 4.07/0.99  --splitting_mode                        input
% 4.07/0.99  --splitting_grd                         true
% 4.07/0.99  --splitting_cvd                         false
% 4.07/0.99  --splitting_cvd_svl                     false
% 4.07/0.99  --splitting_nvd                         32
% 4.07/0.99  --sub_typing                            true
% 4.07/0.99  --prep_gs_sim                           true
% 4.07/0.99  --prep_unflatten                        true
% 4.07/0.99  --prep_res_sim                          true
% 4.07/0.99  --prep_upred                            true
% 4.07/0.99  --prep_sem_filter                       exhaustive
% 4.07/0.99  --prep_sem_filter_out                   false
% 4.07/0.99  --pred_elim                             true
% 4.07/0.99  --res_sim_input                         true
% 4.07/0.99  --eq_ax_congr_red                       true
% 4.07/0.99  --pure_diseq_elim                       true
% 4.07/0.99  --brand_transform                       false
% 4.07/0.99  --non_eq_to_eq                          false
% 4.07/0.99  --prep_def_merge                        true
% 4.07/0.99  --prep_def_merge_prop_impl              false
% 4.07/0.99  --prep_def_merge_mbd                    true
% 4.07/0.99  --prep_def_merge_tr_red                 false
% 4.07/0.99  --prep_def_merge_tr_cl                  false
% 4.07/0.99  --smt_preprocessing                     true
% 4.07/0.99  --smt_ac_axioms                         fast
% 4.07/0.99  --preprocessed_out                      false
% 4.07/0.99  --preprocessed_stats                    false
% 4.07/0.99  
% 4.07/0.99  ------ Abstraction refinement Options
% 4.07/0.99  
% 4.07/0.99  --abstr_ref                             []
% 4.07/0.99  --abstr_ref_prep                        false
% 4.07/0.99  --abstr_ref_until_sat                   false
% 4.07/0.99  --abstr_ref_sig_restrict                funpre
% 4.07/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.07/0.99  --abstr_ref_under                       []
% 4.07/0.99  
% 4.07/0.99  ------ SAT Options
% 4.07/0.99  
% 4.07/0.99  --sat_mode                              false
% 4.07/0.99  --sat_fm_restart_options                ""
% 4.07/0.99  --sat_gr_def                            false
% 4.07/0.99  --sat_epr_types                         true
% 4.07/0.99  --sat_non_cyclic_types                  false
% 4.07/0.99  --sat_finite_models                     false
% 4.07/0.99  --sat_fm_lemmas                         false
% 4.07/0.99  --sat_fm_prep                           false
% 4.07/0.99  --sat_fm_uc_incr                        true
% 4.07/0.99  --sat_out_model                         small
% 4.07/0.99  --sat_out_clauses                       false
% 4.07/0.99  
% 4.07/0.99  ------ QBF Options
% 4.07/0.99  
% 4.07/0.99  --qbf_mode                              false
% 4.07/0.99  --qbf_elim_univ                         false
% 4.07/0.99  --qbf_dom_inst                          none
% 4.07/0.99  --qbf_dom_pre_inst                      false
% 4.07/0.99  --qbf_sk_in                             false
% 4.07/0.99  --qbf_pred_elim                         true
% 4.07/0.99  --qbf_split                             512
% 4.07/0.99  
% 4.07/0.99  ------ BMC1 Options
% 4.07/0.99  
% 4.07/0.99  --bmc1_incremental                      false
% 4.07/0.99  --bmc1_axioms                           reachable_all
% 4.07/0.99  --bmc1_min_bound                        0
% 4.07/0.99  --bmc1_max_bound                        -1
% 4.07/0.99  --bmc1_max_bound_default                -1
% 4.07/0.99  --bmc1_symbol_reachability              true
% 4.07/0.99  --bmc1_property_lemmas                  false
% 4.07/0.99  --bmc1_k_induction                      false
% 4.07/0.99  --bmc1_non_equiv_states                 false
% 4.07/0.99  --bmc1_deadlock                         false
% 4.07/0.99  --bmc1_ucm                              false
% 4.07/0.99  --bmc1_add_unsat_core                   none
% 4.07/0.99  --bmc1_unsat_core_children              false
% 4.07/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.07/0.99  --bmc1_out_stat                         full
% 4.07/0.99  --bmc1_ground_init                      false
% 4.07/0.99  --bmc1_pre_inst_next_state              false
% 4.07/0.99  --bmc1_pre_inst_state                   false
% 4.07/0.99  --bmc1_pre_inst_reach_state             false
% 4.07/0.99  --bmc1_out_unsat_core                   false
% 4.07/0.99  --bmc1_aig_witness_out                  false
% 4.07/0.99  --bmc1_verbose                          false
% 4.07/0.99  --bmc1_dump_clauses_tptp                false
% 4.07/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.07/0.99  --bmc1_dump_file                        -
% 4.07/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.07/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.07/0.99  --bmc1_ucm_extend_mode                  1
% 4.07/0.99  --bmc1_ucm_init_mode                    2
% 4.07/0.99  --bmc1_ucm_cone_mode                    none
% 4.07/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.07/0.99  --bmc1_ucm_relax_model                  4
% 4.07/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.07/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.07/0.99  --bmc1_ucm_layered_model                none
% 4.07/0.99  --bmc1_ucm_max_lemma_size               10
% 4.07/0.99  
% 4.07/0.99  ------ AIG Options
% 4.07/0.99  
% 4.07/0.99  --aig_mode                              false
% 4.07/0.99  
% 4.07/0.99  ------ Instantiation Options
% 4.07/0.99  
% 4.07/0.99  --instantiation_flag                    true
% 4.07/0.99  --inst_sos_flag                         true
% 4.07/0.99  --inst_sos_phase                        true
% 4.07/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.07/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.07/0.99  --inst_lit_sel_side                     num_symb
% 4.07/0.99  --inst_solver_per_active                1400
% 4.07/0.99  --inst_solver_calls_frac                1.
% 4.07/0.99  --inst_passive_queue_type               priority_queues
% 4.07/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.07/0.99  --inst_passive_queues_freq              [25;2]
% 4.07/0.99  --inst_dismatching                      true
% 4.07/0.99  --inst_eager_unprocessed_to_passive     true
% 4.07/0.99  --inst_prop_sim_given                   true
% 4.07/0.99  --inst_prop_sim_new                     false
% 4.07/0.99  --inst_subs_new                         false
% 4.07/0.99  --inst_eq_res_simp                      false
% 4.07/0.99  --inst_subs_given                       false
% 4.07/0.99  --inst_orphan_elimination               true
% 4.07/0.99  --inst_learning_loop_flag               true
% 4.07/0.99  --inst_learning_start                   3000
% 4.07/0.99  --inst_learning_factor                  2
% 4.07/0.99  --inst_start_prop_sim_after_learn       3
% 4.07/0.99  --inst_sel_renew                        solver
% 4.07/0.99  --inst_lit_activity_flag                true
% 4.07/0.99  --inst_restr_to_given                   false
% 4.07/0.99  --inst_activity_threshold               500
% 4.07/0.99  --inst_out_proof                        true
% 4.07/0.99  
% 4.07/0.99  ------ Resolution Options
% 4.07/0.99  
% 4.07/0.99  --resolution_flag                       true
% 4.07/0.99  --res_lit_sel                           adaptive
% 4.07/0.99  --res_lit_sel_side                      none
% 4.07/0.99  --res_ordering                          kbo
% 4.07/0.99  --res_to_prop_solver                    active
% 4.07/0.99  --res_prop_simpl_new                    false
% 4.07/0.99  --res_prop_simpl_given                  true
% 4.07/0.99  --res_passive_queue_type                priority_queues
% 4.07/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.07/0.99  --res_passive_queues_freq               [15;5]
% 4.07/0.99  --res_forward_subs                      full
% 4.07/0.99  --res_backward_subs                     full
% 4.07/0.99  --res_forward_subs_resolution           true
% 4.07/0.99  --res_backward_subs_resolution          true
% 4.07/0.99  --res_orphan_elimination                true
% 4.07/0.99  --res_time_limit                        2.
% 4.07/0.99  --res_out_proof                         true
% 4.07/0.99  
% 4.07/0.99  ------ Superposition Options
% 4.07/0.99  
% 4.07/0.99  --superposition_flag                    true
% 4.07/0.99  --sup_passive_queue_type                priority_queues
% 4.07/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.07/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.07/0.99  --demod_completeness_check              fast
% 4.07/0.99  --demod_use_ground                      true
% 4.07/0.99  --sup_to_prop_solver                    passive
% 4.07/0.99  --sup_prop_simpl_new                    true
% 4.07/0.99  --sup_prop_simpl_given                  true
% 4.07/0.99  --sup_fun_splitting                     true
% 4.07/0.99  --sup_smt_interval                      50000
% 4.07/0.99  
% 4.07/0.99  ------ Superposition Simplification Setup
% 4.07/0.99  
% 4.07/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.07/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.07/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.07/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.07/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.07/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.07/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.07/0.99  --sup_immed_triv                        [TrivRules]
% 4.07/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.99  --sup_immed_bw_main                     []
% 4.07/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.07/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.07/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.99  --sup_input_bw                          []
% 4.07/0.99  
% 4.07/0.99  ------ Combination Options
% 4.07/0.99  
% 4.07/0.99  --comb_res_mult                         3
% 4.07/0.99  --comb_sup_mult                         2
% 4.07/0.99  --comb_inst_mult                        10
% 4.07/0.99  
% 4.07/0.99  ------ Debug Options
% 4.07/0.99  
% 4.07/0.99  --dbg_backtrace                         false
% 4.07/0.99  --dbg_dump_prop_clauses                 false
% 4.07/0.99  --dbg_dump_prop_clauses_file            -
% 4.07/0.99  --dbg_out_stat                          false
% 4.07/0.99  ------ Parsing...
% 4.07/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.07/0.99  
% 4.07/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 4.07/0.99  
% 4.07/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.07/0.99  
% 4.07/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.07/0.99  ------ Proving...
% 4.07/0.99  ------ Problem Properties 
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  clauses                                 23
% 4.07/0.99  conjectures                             2
% 4.07/0.99  EPR                                     8
% 4.07/0.99  Horn                                    18
% 4.07/0.99  unary                                   8
% 4.07/0.99  binary                                  7
% 4.07/0.99  lits                                    50
% 4.07/0.99  lits eq                                 8
% 4.07/0.99  fd_pure                                 0
% 4.07/0.99  fd_pseudo                               0
% 4.07/0.99  fd_cond                                 0
% 4.07/0.99  fd_pseudo_cond                          3
% 4.07/0.99  AC symbols                              0
% 4.07/0.99  
% 4.07/0.99  ------ Schedule dynamic 5 is on 
% 4.07/0.99  
% 4.07/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  ------ 
% 4.07/0.99  Current options:
% 4.07/0.99  ------ 
% 4.07/0.99  
% 4.07/0.99  ------ Input Options
% 4.07/0.99  
% 4.07/0.99  --out_options                           all
% 4.07/0.99  --tptp_safe_out                         true
% 4.07/0.99  --problem_path                          ""
% 4.07/0.99  --include_path                          ""
% 4.07/0.99  --clausifier                            res/vclausify_rel
% 4.07/0.99  --clausifier_options                    ""
% 4.07/0.99  --stdin                                 false
% 4.07/0.99  --stats_out                             all
% 4.07/0.99  
% 4.07/0.99  ------ General Options
% 4.07/0.99  
% 4.07/0.99  --fof                                   false
% 4.07/0.99  --time_out_real                         305.
% 4.07/0.99  --time_out_virtual                      -1.
% 4.07/0.99  --symbol_type_check                     false
% 4.07/0.99  --clausify_out                          false
% 4.07/0.99  --sig_cnt_out                           false
% 4.07/0.99  --trig_cnt_out                          false
% 4.07/0.99  --trig_cnt_out_tolerance                1.
% 4.07/0.99  --trig_cnt_out_sk_spl                   false
% 4.07/0.99  --abstr_cl_out                          false
% 4.07/0.99  
% 4.07/0.99  ------ Global Options
% 4.07/0.99  
% 4.07/0.99  --schedule                              default
% 4.07/0.99  --add_important_lit                     false
% 4.07/0.99  --prop_solver_per_cl                    1000
% 4.07/0.99  --min_unsat_core                        false
% 4.07/0.99  --soft_assumptions                      false
% 4.07/0.99  --soft_lemma_size                       3
% 4.07/0.99  --prop_impl_unit_size                   0
% 4.07/0.99  --prop_impl_unit                        []
% 4.07/0.99  --share_sel_clauses                     true
% 4.07/0.99  --reset_solvers                         false
% 4.07/0.99  --bc_imp_inh                            [conj_cone]
% 4.07/0.99  --conj_cone_tolerance                   3.
% 4.07/0.99  --extra_neg_conj                        none
% 4.07/0.99  --large_theory_mode                     true
% 4.07/0.99  --prolific_symb_bound                   200
% 4.07/0.99  --lt_threshold                          2000
% 4.07/0.99  --clause_weak_htbl                      true
% 4.07/0.99  --gc_record_bc_elim                     false
% 4.07/0.99  
% 4.07/0.99  ------ Preprocessing Options
% 4.07/0.99  
% 4.07/0.99  --preprocessing_flag                    true
% 4.07/0.99  --time_out_prep_mult                    0.1
% 4.07/0.99  --splitting_mode                        input
% 4.07/0.99  --splitting_grd                         true
% 4.07/0.99  --splitting_cvd                         false
% 4.07/0.99  --splitting_cvd_svl                     false
% 4.07/0.99  --splitting_nvd                         32
% 4.07/0.99  --sub_typing                            true
% 4.07/0.99  --prep_gs_sim                           true
% 4.07/0.99  --prep_unflatten                        true
% 4.07/0.99  --prep_res_sim                          true
% 4.07/0.99  --prep_upred                            true
% 4.07/0.99  --prep_sem_filter                       exhaustive
% 4.07/0.99  --prep_sem_filter_out                   false
% 4.07/0.99  --pred_elim                             true
% 4.07/0.99  --res_sim_input                         true
% 4.07/0.99  --eq_ax_congr_red                       true
% 4.07/0.99  --pure_diseq_elim                       true
% 4.07/0.99  --brand_transform                       false
% 4.07/0.99  --non_eq_to_eq                          false
% 4.07/0.99  --prep_def_merge                        true
% 4.07/0.99  --prep_def_merge_prop_impl              false
% 4.07/0.99  --prep_def_merge_mbd                    true
% 4.07/0.99  --prep_def_merge_tr_red                 false
% 4.07/0.99  --prep_def_merge_tr_cl                  false
% 4.07/0.99  --smt_preprocessing                     true
% 4.07/0.99  --smt_ac_axioms                         fast
% 4.07/0.99  --preprocessed_out                      false
% 4.07/0.99  --preprocessed_stats                    false
% 4.07/0.99  
% 4.07/0.99  ------ Abstraction refinement Options
% 4.07/0.99  
% 4.07/0.99  --abstr_ref                             []
% 4.07/0.99  --abstr_ref_prep                        false
% 4.07/0.99  --abstr_ref_until_sat                   false
% 4.07/0.99  --abstr_ref_sig_restrict                funpre
% 4.07/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.07/0.99  --abstr_ref_under                       []
% 4.07/0.99  
% 4.07/0.99  ------ SAT Options
% 4.07/0.99  
% 4.07/0.99  --sat_mode                              false
% 4.07/0.99  --sat_fm_restart_options                ""
% 4.07/0.99  --sat_gr_def                            false
% 4.07/0.99  --sat_epr_types                         true
% 4.07/0.99  --sat_non_cyclic_types                  false
% 4.07/0.99  --sat_finite_models                     false
% 4.07/0.99  --sat_fm_lemmas                         false
% 4.07/0.99  --sat_fm_prep                           false
% 4.07/0.99  --sat_fm_uc_incr                        true
% 4.07/0.99  --sat_out_model                         small
% 4.07/0.99  --sat_out_clauses                       false
% 4.07/0.99  
% 4.07/0.99  ------ QBF Options
% 4.07/0.99  
% 4.07/0.99  --qbf_mode                              false
% 4.07/0.99  --qbf_elim_univ                         false
% 4.07/0.99  --qbf_dom_inst                          none
% 4.07/0.99  --qbf_dom_pre_inst                      false
% 4.07/0.99  --qbf_sk_in                             false
% 4.07/0.99  --qbf_pred_elim                         true
% 4.07/0.99  --qbf_split                             512
% 4.07/0.99  
% 4.07/0.99  ------ BMC1 Options
% 4.07/0.99  
% 4.07/0.99  --bmc1_incremental                      false
% 4.07/0.99  --bmc1_axioms                           reachable_all
% 4.07/0.99  --bmc1_min_bound                        0
% 4.07/0.99  --bmc1_max_bound                        -1
% 4.07/0.99  --bmc1_max_bound_default                -1
% 4.07/0.99  --bmc1_symbol_reachability              true
% 4.07/0.99  --bmc1_property_lemmas                  false
% 4.07/0.99  --bmc1_k_induction                      false
% 4.07/0.99  --bmc1_non_equiv_states                 false
% 4.07/0.99  --bmc1_deadlock                         false
% 4.07/0.99  --bmc1_ucm                              false
% 4.07/0.99  --bmc1_add_unsat_core                   none
% 4.07/0.99  --bmc1_unsat_core_children              false
% 4.07/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.07/0.99  --bmc1_out_stat                         full
% 4.07/0.99  --bmc1_ground_init                      false
% 4.07/0.99  --bmc1_pre_inst_next_state              false
% 4.07/0.99  --bmc1_pre_inst_state                   false
% 4.07/0.99  --bmc1_pre_inst_reach_state             false
% 4.07/0.99  --bmc1_out_unsat_core                   false
% 4.07/0.99  --bmc1_aig_witness_out                  false
% 4.07/0.99  --bmc1_verbose                          false
% 4.07/0.99  --bmc1_dump_clauses_tptp                false
% 4.07/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.07/0.99  --bmc1_dump_file                        -
% 4.07/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.07/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.07/0.99  --bmc1_ucm_extend_mode                  1
% 4.07/0.99  --bmc1_ucm_init_mode                    2
% 4.07/0.99  --bmc1_ucm_cone_mode                    none
% 4.07/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.07/0.99  --bmc1_ucm_relax_model                  4
% 4.07/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.07/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.07/0.99  --bmc1_ucm_layered_model                none
% 4.07/0.99  --bmc1_ucm_max_lemma_size               10
% 4.07/0.99  
% 4.07/0.99  ------ AIG Options
% 4.07/0.99  
% 4.07/0.99  --aig_mode                              false
% 4.07/0.99  
% 4.07/0.99  ------ Instantiation Options
% 4.07/0.99  
% 4.07/0.99  --instantiation_flag                    true
% 4.07/0.99  --inst_sos_flag                         true
% 4.07/0.99  --inst_sos_phase                        true
% 4.07/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.07/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.07/0.99  --inst_lit_sel_side                     none
% 4.07/0.99  --inst_solver_per_active                1400
% 4.07/0.99  --inst_solver_calls_frac                1.
% 4.07/0.99  --inst_passive_queue_type               priority_queues
% 4.07/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.07/0.99  --inst_passive_queues_freq              [25;2]
% 4.07/0.99  --inst_dismatching                      true
% 4.07/0.99  --inst_eager_unprocessed_to_passive     true
% 4.07/0.99  --inst_prop_sim_given                   true
% 4.07/0.99  --inst_prop_sim_new                     false
% 4.07/0.99  --inst_subs_new                         false
% 4.07/0.99  --inst_eq_res_simp                      false
% 4.07/0.99  --inst_subs_given                       false
% 4.07/0.99  --inst_orphan_elimination               true
% 4.07/0.99  --inst_learning_loop_flag               true
% 4.07/0.99  --inst_learning_start                   3000
% 4.07/0.99  --inst_learning_factor                  2
% 4.07/0.99  --inst_start_prop_sim_after_learn       3
% 4.07/0.99  --inst_sel_renew                        solver
% 4.07/0.99  --inst_lit_activity_flag                true
% 4.07/0.99  --inst_restr_to_given                   false
% 4.07/0.99  --inst_activity_threshold               500
% 4.07/0.99  --inst_out_proof                        true
% 4.07/0.99  
% 4.07/0.99  ------ Resolution Options
% 4.07/0.99  
% 4.07/0.99  --resolution_flag                       false
% 4.07/0.99  --res_lit_sel                           adaptive
% 4.07/0.99  --res_lit_sel_side                      none
% 4.07/0.99  --res_ordering                          kbo
% 4.07/0.99  --res_to_prop_solver                    active
% 4.07/0.99  --res_prop_simpl_new                    false
% 4.07/0.99  --res_prop_simpl_given                  true
% 4.07/0.99  --res_passive_queue_type                priority_queues
% 4.07/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.07/0.99  --res_passive_queues_freq               [15;5]
% 4.07/0.99  --res_forward_subs                      full
% 4.07/0.99  --res_backward_subs                     full
% 4.07/0.99  --res_forward_subs_resolution           true
% 4.07/0.99  --res_backward_subs_resolution          true
% 4.07/0.99  --res_orphan_elimination                true
% 4.07/0.99  --res_time_limit                        2.
% 4.07/0.99  --res_out_proof                         true
% 4.07/0.99  
% 4.07/0.99  ------ Superposition Options
% 4.07/0.99  
% 4.07/0.99  --superposition_flag                    true
% 4.07/0.99  --sup_passive_queue_type                priority_queues
% 4.07/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.07/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.07/0.99  --demod_completeness_check              fast
% 4.07/0.99  --demod_use_ground                      true
% 4.07/0.99  --sup_to_prop_solver                    passive
% 4.07/0.99  --sup_prop_simpl_new                    true
% 4.07/0.99  --sup_prop_simpl_given                  true
% 4.07/0.99  --sup_fun_splitting                     true
% 4.07/0.99  --sup_smt_interval                      50000
% 4.07/0.99  
% 4.07/0.99  ------ Superposition Simplification Setup
% 4.07/0.99  
% 4.07/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.07/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.07/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.07/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.07/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.07/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.07/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.07/0.99  --sup_immed_triv                        [TrivRules]
% 4.07/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.99  --sup_immed_bw_main                     []
% 4.07/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.07/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.07/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.99  --sup_input_bw                          []
% 4.07/0.99  
% 4.07/0.99  ------ Combination Options
% 4.07/0.99  
% 4.07/0.99  --comb_res_mult                         3
% 4.07/0.99  --comb_sup_mult                         2
% 4.07/0.99  --comb_inst_mult                        10
% 4.07/0.99  
% 4.07/0.99  ------ Debug Options
% 4.07/0.99  
% 4.07/0.99  --dbg_backtrace                         false
% 4.07/0.99  --dbg_dump_prop_clauses                 false
% 4.07/0.99  --dbg_dump_prop_clauses_file            -
% 4.07/0.99  --dbg_out_stat                          false
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  ------ Proving...
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  % SZS status Theorem for theBenchmark.p
% 4.07/0.99  
% 4.07/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.07/0.99  
% 4.07/0.99  fof(f2,axiom,(
% 4.07/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f12,plain,(
% 4.07/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.07/0.99    inference(rectify,[],[f2])).
% 4.07/0.99  
% 4.07/0.99  fof(f15,plain,(
% 4.07/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 4.07/0.99    inference(ennf_transformation,[],[f12])).
% 4.07/0.99  
% 4.07/0.99  fof(f34,plain,(
% 4.07/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 4.07/0.99    introduced(choice_axiom,[])).
% 4.07/0.99  
% 4.07/0.99  fof(f35,plain,(
% 4.07/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 4.07/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f34])).
% 4.07/0.99  
% 4.07/0.99  fof(f56,plain,(
% 4.07/0.99    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f35])).
% 4.07/0.99  
% 4.07/0.99  fof(f3,axiom,(
% 4.07/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f16,plain,(
% 4.07/0.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.07/0.99    inference(ennf_transformation,[],[f3])).
% 4.07/0.99  
% 4.07/0.99  fof(f59,plain,(
% 4.07/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f16])).
% 4.07/0.99  
% 4.07/0.99  fof(f26,plain,(
% 4.07/0.99    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 4.07/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 4.07/0.99  
% 4.07/0.99  fof(f37,plain,(
% 4.07/0.99    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 4.07/0.99    inference(nnf_transformation,[],[f26])).
% 4.07/0.99  
% 4.07/0.99  fof(f38,plain,(
% 4.07/0.99    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 4.07/0.99    inference(flattening,[],[f37])).
% 4.07/0.99  
% 4.07/0.99  fof(f39,plain,(
% 4.07/0.99    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 4.07/0.99    inference(rectify,[],[f38])).
% 4.07/0.99  
% 4.07/0.99  fof(f42,plain,(
% 4.07/0.99    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 4.07/0.99    introduced(choice_axiom,[])).
% 4.07/0.99  
% 4.07/0.99  fof(f41,plain,(
% 4.07/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK5(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 4.07/0.99    introduced(choice_axiom,[])).
% 4.07/0.99  
% 4.07/0.99  fof(f40,plain,(
% 4.07/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK4(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK4(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK4(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.07/0.99    introduced(choice_axiom,[])).
% 4.07/0.99  
% 4.07/0.99  fof(f43,plain,(
% 4.07/0.99    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK4(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0)) = sK4(X0,X1) & r2_hidden(sK5(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK4(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 4.07/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f42,f41,f40])).
% 4.07/0.99  
% 4.07/0.99  fof(f63,plain,(
% 4.07/0.99    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f43])).
% 4.07/0.99  
% 4.07/0.99  fof(f7,axiom,(
% 4.07/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f20,plain,(
% 4.07/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.07/0.99    inference(ennf_transformation,[],[f7])).
% 4.07/0.99  
% 4.07/0.99  fof(f75,plain,(
% 4.07/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f20])).
% 4.07/0.99  
% 4.07/0.99  fof(f10,conjecture,(
% 4.07/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f11,negated_conjecture,(
% 4.07/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 4.07/0.99    inference(negated_conjecture,[],[f10])).
% 4.07/0.99  
% 4.07/0.99  fof(f13,plain,(
% 4.07/0.99    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 4.07/0.99    inference(pure_predicate_removal,[],[f11])).
% 4.07/0.99  
% 4.07/0.99  fof(f14,plain,(
% 4.07/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 4.07/0.99    inference(pure_predicate_removal,[],[f13])).
% 4.07/0.99  
% 4.07/0.99  fof(f24,plain,(
% 4.07/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 4.07/0.99    inference(ennf_transformation,[],[f14])).
% 4.07/0.99  
% 4.07/0.99  fof(f25,plain,(
% 4.07/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 4.07/0.99    inference(flattening,[],[f24])).
% 4.07/0.99  
% 4.07/0.99  fof(f48,plain,(
% 4.07/0.99    ( ! [X2,X0,X1] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) => ((r1_tsep_1(sK10,X2) | r1_tsep_1(X2,sK10)) & (~r1_tsep_1(sK10,X1) | ~r1_tsep_1(X1,sK10)) & m1_pre_topc(X1,X2) & m1_pre_topc(sK10,X0))) )),
% 4.07/0.99    introduced(choice_axiom,[])).
% 4.07/0.99  
% 4.07/0.99  fof(f47,plain,(
% 4.07/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) => (? [X3] : ((r1_tsep_1(X3,sK9) | r1_tsep_1(sK9,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,sK9) & m1_pre_topc(X3,X0)) & m1_pre_topc(sK9,X0))) )),
% 4.07/0.99    introduced(choice_axiom,[])).
% 4.07/0.99  
% 4.07/0.99  fof(f46,plain,(
% 4.07/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) => (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK8) | ~r1_tsep_1(sK8,X3)) & m1_pre_topc(sK8,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(sK8,X0))) )),
% 4.07/0.99    introduced(choice_axiom,[])).
% 4.07/0.99  
% 4.07/0.99  fof(f45,plain,(
% 4.07/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK7)) & m1_pre_topc(X2,sK7)) & m1_pre_topc(X1,sK7)) & l1_pre_topc(sK7))),
% 4.07/0.99    introduced(choice_axiom,[])).
% 4.07/0.99  
% 4.07/0.99  fof(f49,plain,(
% 4.07/0.99    ((((r1_tsep_1(sK10,sK9) | r1_tsep_1(sK9,sK10)) & (~r1_tsep_1(sK10,sK8) | ~r1_tsep_1(sK8,sK10)) & m1_pre_topc(sK8,sK9) & m1_pre_topc(sK10,sK7)) & m1_pre_topc(sK9,sK7)) & m1_pre_topc(sK8,sK7)) & l1_pre_topc(sK7)),
% 4.07/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f25,f48,f47,f46,f45])).
% 4.07/0.99  
% 4.07/0.99  fof(f81,plain,(
% 4.07/0.99    m1_pre_topc(sK9,sK7)),
% 4.07/0.99    inference(cnf_transformation,[],[f49])).
% 4.07/0.99  
% 4.07/0.99  fof(f79,plain,(
% 4.07/0.99    l1_pre_topc(sK7)),
% 4.07/0.99    inference(cnf_transformation,[],[f49])).
% 4.07/0.99  
% 4.07/0.99  fof(f5,axiom,(
% 4.07/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f18,plain,(
% 4.07/0.99    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 4.07/0.99    inference(ennf_transformation,[],[f5])).
% 4.07/0.99  
% 4.07/0.99  fof(f27,plain,(
% 4.07/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 4.07/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 4.07/0.99  
% 4.07/0.99  fof(f28,plain,(
% 4.07/0.99    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 4.07/0.99    inference(definition_folding,[],[f18,f27,f26])).
% 4.07/0.99  
% 4.07/0.99  fof(f73,plain,(
% 4.07/0.99    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f28])).
% 4.07/0.99  
% 4.07/0.99  fof(f36,plain,(
% 4.07/0.99    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 4.07/0.99    inference(nnf_transformation,[],[f27])).
% 4.07/0.99  
% 4.07/0.99  fof(f61,plain,(
% 4.07/0.99    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f36])).
% 4.07/0.99  
% 4.07/0.99  fof(f83,plain,(
% 4.07/0.99    m1_pre_topc(sK8,sK9)),
% 4.07/0.99    inference(cnf_transformation,[],[f49])).
% 4.07/0.99  
% 4.07/0.99  fof(f1,axiom,(
% 4.07/0.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f29,plain,(
% 4.07/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.07/0.99    inference(nnf_transformation,[],[f1])).
% 4.07/0.99  
% 4.07/0.99  fof(f30,plain,(
% 4.07/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.07/0.99    inference(flattening,[],[f29])).
% 4.07/0.99  
% 4.07/0.99  fof(f31,plain,(
% 4.07/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.07/0.99    inference(rectify,[],[f30])).
% 4.07/0.99  
% 4.07/0.99  fof(f32,plain,(
% 4.07/0.99    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 4.07/0.99    introduced(choice_axiom,[])).
% 4.07/0.99  
% 4.07/0.99  fof(f33,plain,(
% 4.07/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.07/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 4.07/0.99  
% 4.07/0.99  fof(f51,plain,(
% 4.07/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 4.07/0.99    inference(cnf_transformation,[],[f33])).
% 4.07/0.99  
% 4.07/0.99  fof(f87,plain,(
% 4.07/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 4.07/0.99    inference(equality_resolution,[],[f51])).
% 4.07/0.99  
% 4.07/0.99  fof(f57,plain,(
% 4.07/0.99    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f35])).
% 4.07/0.99  
% 4.07/0.99  fof(f6,axiom,(
% 4.07/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f19,plain,(
% 4.07/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 4.07/0.99    inference(ennf_transformation,[],[f6])).
% 4.07/0.99  
% 4.07/0.99  fof(f74,plain,(
% 4.07/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f19])).
% 4.07/0.99  
% 4.07/0.99  fof(f4,axiom,(
% 4.07/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f17,plain,(
% 4.07/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 4.07/0.99    inference(ennf_transformation,[],[f4])).
% 4.07/0.99  
% 4.07/0.99  fof(f60,plain,(
% 4.07/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f17])).
% 4.07/0.99  
% 4.07/0.99  fof(f8,axiom,(
% 4.07/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f21,plain,(
% 4.07/0.99    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 4.07/0.99    inference(ennf_transformation,[],[f8])).
% 4.07/0.99  
% 4.07/0.99  fof(f44,plain,(
% 4.07/0.99    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 4.07/0.99    inference(nnf_transformation,[],[f21])).
% 4.07/0.99  
% 4.07/0.99  fof(f76,plain,(
% 4.07/0.99    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f44])).
% 4.07/0.99  
% 4.07/0.99  fof(f58,plain,(
% 4.07/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f35])).
% 4.07/0.99  
% 4.07/0.99  fof(f85,plain,(
% 4.07/0.99    r1_tsep_1(sK10,sK9) | r1_tsep_1(sK9,sK10)),
% 4.07/0.99    inference(cnf_transformation,[],[f49])).
% 4.07/0.99  
% 4.07/0.99  fof(f9,axiom,(
% 4.07/0.99    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f22,plain,(
% 4.07/0.99    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 4.07/0.99    inference(ennf_transformation,[],[f9])).
% 4.07/0.99  
% 4.07/0.99  fof(f23,plain,(
% 4.07/0.99    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 4.07/0.99    inference(flattening,[],[f22])).
% 4.07/0.99  
% 4.07/0.99  fof(f78,plain,(
% 4.07/0.99    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f23])).
% 4.07/0.99  
% 4.07/0.99  fof(f82,plain,(
% 4.07/0.99    m1_pre_topc(sK10,sK7)),
% 4.07/0.99    inference(cnf_transformation,[],[f49])).
% 4.07/0.99  
% 4.07/0.99  fof(f84,plain,(
% 4.07/0.99    ~r1_tsep_1(sK10,sK8) | ~r1_tsep_1(sK8,sK10)),
% 4.07/0.99    inference(cnf_transformation,[],[f49])).
% 4.07/0.99  
% 4.07/0.99  fof(f77,plain,(
% 4.07/0.99    ( ! [X0,X1] : (r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f44])).
% 4.07/0.99  
% 4.07/0.99  cnf(c_8,plain,
% 4.07/0.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f56]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1602,plain,
% 4.07/0.99      ( r1_xboole_0(X0,X1) = iProver_top
% 4.07/0.99      | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_9,plain,
% 4.07/0.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 4.07/0.99      inference(cnf_transformation,[],[f59]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_22,plain,
% 4.07/0.99      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 4.07/0.99      inference(cnf_transformation,[],[f63]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_442,plain,
% 4.07/0.99      ( ~ sP0(X0,X1)
% 4.07/0.99      | k2_xboole_0(X2,X3) = X3
% 4.07/0.99      | k2_struct_0(X1) != X3
% 4.07/0.99      | k2_struct_0(X0) != X2 ),
% 4.07/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_443,plain,
% 4.07/0.99      ( ~ sP0(X0,X1)
% 4.07/0.99      | k2_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X1) ),
% 4.07/0.99      inference(unflattening,[status(thm)],[c_442]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_25,plain,
% 4.07/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f75]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_33,negated_conjecture,
% 4.07/0.99      ( m1_pre_topc(sK9,sK7) ),
% 4.07/0.99      inference(cnf_transformation,[],[f81]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_649,plain,
% 4.07/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK7 != X0 | sK9 != X1 ),
% 4.07/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_650,plain,
% 4.07/0.99      ( ~ l1_pre_topc(sK7) | l1_pre_topc(sK9) ),
% 4.07/0.99      inference(unflattening,[status(thm)],[c_649]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_35,negated_conjecture,
% 4.07/0.99      ( l1_pre_topc(sK7) ),
% 4.07/0.99      inference(cnf_transformation,[],[f79]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_652,plain,
% 4.07/0.99      ( l1_pre_topc(sK9) ),
% 4.07/0.99      inference(global_propositional_subsumption,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_650,c_35]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_23,plain,
% 4.07/0.99      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f73]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_12,plain,
% 4.07/0.99      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f61]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_394,plain,
% 4.07/0.99      ( sP0(X0,X1)
% 4.07/0.99      | ~ m1_pre_topc(X0,X1)
% 4.07/0.99      | ~ l1_pre_topc(X1)
% 4.07/0.99      | ~ l1_pre_topc(X0) ),
% 4.07/0.99      inference(resolution,[status(thm)],[c_23,c_12]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_398,plain,
% 4.07/0.99      ( ~ l1_pre_topc(X1) | ~ m1_pre_topc(X0,X1) | sP0(X0,X1) ),
% 4.07/0.99      inference(global_propositional_subsumption,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_394,c_25]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_399,plain,
% 4.07/0.99      ( sP0(X0,X1) | ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) ),
% 4.07/0.99      inference(renaming,[status(thm)],[c_398]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_31,negated_conjecture,
% 4.07/0.99      ( m1_pre_topc(sK8,sK9) ),
% 4.07/0.99      inference(cnf_transformation,[],[f83]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_596,plain,
% 4.07/0.99      ( sP0(X0,X1) | ~ l1_pre_topc(X1) | sK8 != X0 | sK9 != X1 ),
% 4.07/0.99      inference(resolution_lifted,[status(thm)],[c_399,c_31]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_597,plain,
% 4.07/0.99      ( sP0(sK8,sK9) | ~ l1_pre_topc(sK9) ),
% 4.07/0.99      inference(unflattening,[status(thm)],[c_596]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_659,plain,
% 4.07/0.99      ( sP0(sK8,sK9) ),
% 4.07/0.99      inference(backward_subsumption_resolution,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_652,c_597]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_916,plain,
% 4.07/0.99      ( k2_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X1)
% 4.07/0.99      | sK8 != X0
% 4.07/0.99      | sK9 != X1 ),
% 4.07/0.99      inference(resolution_lifted,[status(thm)],[c_443,c_659]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_917,plain,
% 4.07/0.99      ( k2_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) = k2_struct_0(sK9) ),
% 4.07/0.99      inference(unflattening,[status(thm)],[c_916]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_4,plain,
% 4.07/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 4.07/0.99      inference(cnf_transformation,[],[f87]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1606,plain,
% 4.07/0.99      ( r2_hidden(X0,X1) != iProver_top
% 4.07/0.99      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2176,plain,
% 4.07/0.99      ( r2_hidden(X0,k2_struct_0(sK8)) != iProver_top
% 4.07/0.99      | r2_hidden(X0,k2_struct_0(sK9)) = iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_917,c_1606]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2596,plain,
% 4.07/0.99      ( r1_xboole_0(k2_struct_0(sK8),X0) = iProver_top
% 4.07/0.99      | r2_hidden(sK3(k2_struct_0(sK8),X0),k2_struct_0(sK9)) = iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_1602,c_2176]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_7,plain,
% 4.07/0.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X1) ),
% 4.07/0.99      inference(cnf_transformation,[],[f57]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1603,plain,
% 4.07/0.99      ( r1_xboole_0(X0,X1) = iProver_top
% 4.07/0.99      | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_24,plain,
% 4.07/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f74]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_705,plain,
% 4.07/0.99      ( l1_struct_0(X0) | sK9 != X0 ),
% 4.07/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_652]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_706,plain,
% 4.07/0.99      ( l1_struct_0(sK9) ),
% 4.07/0.99      inference(unflattening,[status(thm)],[c_705]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1593,plain,
% 4.07/0.99      ( l1_struct_0(sK9) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_10,plain,
% 4.07/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f60]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1601,plain,
% 4.07/0.99      ( u1_struct_0(X0) = k2_struct_0(X0)
% 4.07/0.99      | l1_struct_0(X0) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2008,plain,
% 4.07/0.99      ( u1_struct_0(sK9) = k2_struct_0(sK9) ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_1593,c_1601]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_27,plain,
% 4.07/0.99      ( ~ r1_tsep_1(X0,X1)
% 4.07/0.99      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 4.07/0.99      | ~ l1_struct_0(X0)
% 4.07/0.99      | ~ l1_struct_0(X1) ),
% 4.07/0.99      inference(cnf_transformation,[],[f76]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1599,plain,
% 4.07/0.99      ( r1_tsep_1(X0,X1) != iProver_top
% 4.07/0.99      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 4.07/0.99      | l1_struct_0(X0) != iProver_top
% 4.07/0.99      | l1_struct_0(X1) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_3202,plain,
% 4.07/0.99      ( r1_tsep_1(sK9,X0) != iProver_top
% 4.07/0.99      | r1_xboole_0(k2_struct_0(sK9),u1_struct_0(X0)) = iProver_top
% 4.07/0.99      | l1_struct_0(X0) != iProver_top
% 4.07/0.99      | l1_struct_0(sK9) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_2008,c_1599]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_707,plain,
% 4.07/0.99      ( l1_struct_0(sK9) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_5485,plain,
% 4.07/0.99      ( l1_struct_0(X0) != iProver_top
% 4.07/0.99      | r1_xboole_0(k2_struct_0(sK9),u1_struct_0(X0)) = iProver_top
% 4.07/0.99      | r1_tsep_1(sK9,X0) != iProver_top ),
% 4.07/0.99      inference(global_propositional_subsumption,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_3202,c_707]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_5486,plain,
% 4.07/0.99      ( r1_tsep_1(sK9,X0) != iProver_top
% 4.07/0.99      | r1_xboole_0(k2_struct_0(sK9),u1_struct_0(X0)) = iProver_top
% 4.07/0.99      | l1_struct_0(X0) != iProver_top ),
% 4.07/0.99      inference(renaming,[status(thm)],[c_5485]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_6,plain,
% 4.07/0.99      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f58]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1604,plain,
% 4.07/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 4.07/0.99      | r2_hidden(X2,X1) != iProver_top
% 4.07/0.99      | r2_hidden(X2,X0) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_5495,plain,
% 4.07/0.99      ( r1_tsep_1(sK9,X0) != iProver_top
% 4.07/0.99      | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
% 4.07/0.99      | r2_hidden(X1,k2_struct_0(sK9)) != iProver_top
% 4.07/0.99      | l1_struct_0(X0) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_5486,c_1604]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_12421,plain,
% 4.07/0.99      ( r1_tsep_1(sK9,X0) != iProver_top
% 4.07/0.99      | r1_xboole_0(X1,u1_struct_0(X0)) = iProver_top
% 4.07/0.99      | r2_hidden(sK3(X1,u1_struct_0(X0)),k2_struct_0(sK9)) != iProver_top
% 4.07/0.99      | l1_struct_0(X0) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_1603,c_5495]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_17529,plain,
% 4.07/0.99      ( r1_tsep_1(sK9,X0) != iProver_top
% 4.07/0.99      | r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X0)) = iProver_top
% 4.07/0.99      | l1_struct_0(X0) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_2596,c_12421]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_17541,plain,
% 4.07/0.99      ( r1_tsep_1(sK9,sK10) != iProver_top
% 4.07/0.99      | r1_xboole_0(k2_struct_0(sK8),u1_struct_0(sK10)) = iProver_top
% 4.07/0.99      | l1_struct_0(sK10) != iProver_top ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_17529]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_29,negated_conjecture,
% 4.07/0.99      ( r1_tsep_1(sK9,sK10) | r1_tsep_1(sK10,sK9) ),
% 4.07/0.99      inference(cnf_transformation,[],[f85]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1597,plain,
% 4.07/0.99      ( r1_tsep_1(sK9,sK10) = iProver_top
% 4.07/0.99      | r1_tsep_1(sK10,sK9) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_28,plain,
% 4.07/0.99      ( ~ r1_tsep_1(X0,X1)
% 4.07/0.99      | r1_tsep_1(X1,X0)
% 4.07/0.99      | ~ l1_struct_0(X0)
% 4.07/0.99      | ~ l1_struct_0(X1) ),
% 4.07/0.99      inference(cnf_transformation,[],[f78]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1598,plain,
% 4.07/0.99      ( r1_tsep_1(X0,X1) != iProver_top
% 4.07/0.99      | r1_tsep_1(X1,X0) = iProver_top
% 4.07/0.99      | l1_struct_0(X0) != iProver_top
% 4.07/0.99      | l1_struct_0(X1) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2604,plain,
% 4.07/0.99      ( r1_tsep_1(sK10,sK9) = iProver_top
% 4.07/0.99      | l1_struct_0(sK9) != iProver_top
% 4.07/0.99      | l1_struct_0(sK10) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_1597,c_1598]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_36,plain,
% 4.07/0.99      ( l1_pre_topc(sK7) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_51,plain,
% 4.07/0.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_53,plain,
% 4.07/0.99      ( l1_pre_topc(sK10) != iProver_top
% 4.07/0.99      | l1_struct_0(sK10) = iProver_top ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_51]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_32,negated_conjecture,
% 4.07/0.99      ( m1_pre_topc(sK10,sK7) ),
% 4.07/0.99      inference(cnf_transformation,[],[f82]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_627,plain,
% 4.07/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK7 != X0 | sK10 != X1 ),
% 4.07/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_32]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_628,plain,
% 4.07/0.99      ( ~ l1_pre_topc(sK7) | l1_pre_topc(sK10) ),
% 4.07/0.99      inference(unflattening,[status(thm)],[c_627]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_629,plain,
% 4.07/0.99      ( l1_pre_topc(sK7) != iProver_top
% 4.07/0.99      | l1_pre_topc(sK10) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_628]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2898,plain,
% 4.07/0.99      ( r1_tsep_1(sK10,sK9) = iProver_top ),
% 4.07/0.99      inference(global_propositional_subsumption,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_2604,c_36,c_53,c_629,c_707]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2902,plain,
% 4.07/0.99      ( r1_tsep_1(sK9,sK10) = iProver_top
% 4.07/0.99      | l1_struct_0(sK9) != iProver_top
% 4.07/0.99      | l1_struct_0(sK10) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_2898,c_1598]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1261,plain,( X0 = X0 ),theory(equality) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2126,plain,
% 4.07/0.99      ( u1_struct_0(sK10) = u1_struct_0(sK10) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_1261]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1265,plain,
% 4.07/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.07/0.99      theory(equality) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1662,plain,
% 4.07/0.99      ( ~ r1_xboole_0(X0,X1)
% 4.07/0.99      | r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10))
% 4.07/0.99      | u1_struct_0(sK8) != X0
% 4.07/0.99      | u1_struct_0(sK10) != X1 ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_1265]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1733,plain,
% 4.07/0.99      ( r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10))
% 4.07/0.99      | ~ r1_xboole_0(k2_struct_0(sK8),X0)
% 4.07/0.99      | u1_struct_0(sK8) != k2_struct_0(sK8)
% 4.07/0.99      | u1_struct_0(sK10) != X0 ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_1662]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2068,plain,
% 4.07/0.99      ( r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10))
% 4.07/0.99      | ~ r1_xboole_0(k2_struct_0(sK8),u1_struct_0(sK10))
% 4.07/0.99      | u1_struct_0(sK8) != k2_struct_0(sK8)
% 4.07/0.99      | u1_struct_0(sK10) != u1_struct_0(sK10) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_1733]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2071,plain,
% 4.07/0.99      ( u1_struct_0(sK8) != k2_struct_0(sK8)
% 4.07/0.99      | u1_struct_0(sK10) != u1_struct_0(sK10)
% 4.07/0.99      | r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10)) = iProver_top
% 4.07/0.99      | r1_xboole_0(k2_struct_0(sK8),u1_struct_0(sK10)) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_2068]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1879,plain,
% 4.07/0.99      ( ~ l1_struct_0(sK8) | u1_struct_0(sK8) = k2_struct_0(sK8) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1670,plain,
% 4.07/0.99      ( ~ r1_tsep_1(sK8,sK10)
% 4.07/0.99      | r1_tsep_1(sK10,sK8)
% 4.07/0.99      | ~ l1_struct_0(sK8)
% 4.07/0.99      | ~ l1_struct_0(sK10) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_28]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1671,plain,
% 4.07/0.99      ( r1_tsep_1(sK8,sK10) != iProver_top
% 4.07/0.99      | r1_tsep_1(sK10,sK8) = iProver_top
% 4.07/0.99      | l1_struct_0(sK8) != iProver_top
% 4.07/0.99      | l1_struct_0(sK10) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_1670]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_30,negated_conjecture,
% 4.07/0.99      ( ~ r1_tsep_1(sK8,sK10) | ~ r1_tsep_1(sK10,sK8) ),
% 4.07/0.99      inference(cnf_transformation,[],[f84]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1596,plain,
% 4.07/0.99      ( r1_tsep_1(sK8,sK10) != iProver_top
% 4.07/0.99      | r1_tsep_1(sK10,sK8) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_41,plain,
% 4.07/0.99      ( r1_tsep_1(sK8,sK10) != iProver_top
% 4.07/0.99      | r1_tsep_1(sK10,sK8) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_606,plain,
% 4.07/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK8 != X1 | sK9 != X0 ),
% 4.07/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_31]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_607,plain,
% 4.07/0.99      ( l1_pre_topc(sK8) | ~ l1_pre_topc(sK9) ),
% 4.07/0.99      inference(unflattening,[status(thm)],[c_606]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_660,plain,
% 4.07/0.99      ( l1_pre_topc(sK8) ),
% 4.07/0.99      inference(backward_subsumption_resolution,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_652,c_607]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_712,plain,
% 4.07/0.99      ( l1_struct_0(X0) | sK8 != X0 ),
% 4.07/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_660]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_713,plain,
% 4.07/0.99      ( l1_struct_0(sK8) ),
% 4.07/0.99      inference(unflattening,[status(thm)],[c_712]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_714,plain,
% 4.07/0.99      ( l1_struct_0(sK8) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_713]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1639,plain,
% 4.07/0.99      ( r1_tsep_1(sK8,sK10)
% 4.07/0.99      | ~ r1_tsep_1(sK10,sK8)
% 4.07/0.99      | ~ l1_struct_0(sK8)
% 4.07/0.99      | ~ l1_struct_0(sK10) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_28]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1640,plain,
% 4.07/0.99      ( r1_tsep_1(sK8,sK10) = iProver_top
% 4.07/0.99      | r1_tsep_1(sK10,sK8) != iProver_top
% 4.07/0.99      | l1_struct_0(sK8) != iProver_top
% 4.07/0.99      | l1_struct_0(sK10) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_1639]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1648,plain,
% 4.07/0.99      ( r1_tsep_1(sK10,sK8) != iProver_top ),
% 4.07/0.99      inference(global_propositional_subsumption,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_1596,c_36,c_41,c_53,c_629,c_714,c_1640]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_26,plain,
% 4.07/0.99      ( r1_tsep_1(X0,X1)
% 4.07/0.99      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 4.07/0.99      | ~ l1_struct_0(X0)
% 4.07/0.99      | ~ l1_struct_0(X1) ),
% 4.07/0.99      inference(cnf_transformation,[],[f77]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1636,plain,
% 4.07/0.99      ( r1_tsep_1(sK8,sK10)
% 4.07/0.99      | ~ r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10))
% 4.07/0.99      | ~ l1_struct_0(sK8)
% 4.07/0.99      | ~ l1_struct_0(sK10) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_26]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1637,plain,
% 4.07/0.99      ( r1_tsep_1(sK8,sK10) = iProver_top
% 4.07/0.99      | r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10)) != iProver_top
% 4.07/0.99      | l1_struct_0(sK8) != iProver_top
% 4.07/0.99      | l1_struct_0(sK10) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_1636]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(contradiction,plain,
% 4.07/0.99      ( $false ),
% 4.07/0.99      inference(minisat,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_17541,c_2902,c_2126,c_2071,c_1879,c_1671,c_1648,
% 4.07/0.99                 c_1637,c_714,c_713,c_707,c_629,c_53,c_36]) ).
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.07/0.99  
% 4.07/0.99  ------                               Statistics
% 4.07/0.99  
% 4.07/0.99  ------ General
% 4.07/0.99  
% 4.07/0.99  abstr_ref_over_cycles:                  0
% 4.07/0.99  abstr_ref_under_cycles:                 0
% 4.07/0.99  gc_basic_clause_elim:                   0
% 4.07/0.99  forced_gc_time:                         0
% 4.07/0.99  parsing_time:                           0.007
% 4.07/0.99  unif_index_cands_time:                  0.
% 4.07/0.99  unif_index_add_time:                    0.
% 4.07/0.99  orderings_time:                         0.
% 4.07/0.99  out_proof_time:                         0.01
% 4.07/0.99  total_time:                             0.48
% 4.07/0.99  num_of_symbols:                         56
% 4.07/0.99  num_of_terms:                           18898
% 4.07/0.99  
% 4.07/0.99  ------ Preprocessing
% 4.07/0.99  
% 4.07/0.99  num_of_splits:                          0
% 4.07/0.99  num_of_split_atoms:                     0
% 4.07/0.99  num_of_reused_defs:                     0
% 4.07/0.99  num_eq_ax_congr_red:                    47
% 4.07/0.99  num_of_sem_filtered_clauses:            6
% 4.07/0.99  num_of_subtypes:                        0
% 4.07/0.99  monotx_restored_types:                  0
% 4.07/0.99  sat_num_of_epr_types:                   0
% 4.07/0.99  sat_num_of_non_cyclic_types:            0
% 4.07/0.99  sat_guarded_non_collapsed_types:        0
% 4.07/0.99  num_pure_diseq_elim:                    0
% 4.07/0.99  simp_replaced_by:                       0
% 4.07/0.99  res_preprocessed:                       151
% 4.07/0.99  prep_upred:                             0
% 4.07/0.99  prep_unflattend:                        48
% 4.07/0.99  smt_new_axioms:                         0
% 4.07/0.99  pred_elim_cands:                        4
% 4.07/0.99  pred_elim:                              5
% 4.07/0.99  pred_elim_cl:                           8
% 4.07/0.99  pred_elim_cycles:                       9
% 4.07/0.99  merged_defs:                            0
% 4.07/0.99  merged_defs_ncl:                        0
% 4.07/0.99  bin_hyper_res:                          0
% 4.07/0.99  prep_cycles:                            5
% 4.07/0.99  pred_elim_time:                         0.005
% 4.07/0.99  splitting_time:                         0.
% 4.07/0.99  sem_filter_time:                        0.
% 4.07/0.99  monotx_time:                            0.
% 4.07/0.99  subtype_inf_time:                       0.
% 4.07/0.99  
% 4.07/0.99  ------ Problem properties
% 4.07/0.99  
% 4.07/0.99  clauses:                                23
% 4.07/0.99  conjectures:                            2
% 4.07/0.99  epr:                                    8
% 4.07/0.99  horn:                                   18
% 4.07/0.99  ground:                                 10
% 4.07/0.99  unary:                                  8
% 4.07/0.99  binary:                                 7
% 4.07/0.99  lits:                                   50
% 4.07/0.99  lits_eq:                                8
% 4.07/0.99  fd_pure:                                0
% 4.07/0.99  fd_pseudo:                              0
% 4.07/0.99  fd_cond:                                0
% 4.07/0.99  fd_pseudo_cond:                         3
% 4.07/0.99  ac_symbols:                             0
% 4.07/0.99  
% 4.07/0.99  ------ Propositional Solver
% 4.07/0.99  
% 4.07/0.99  prop_solver_calls:                      38
% 4.07/0.99  prop_fast_solver_calls:                 1516
% 4.07/0.99  smt_solver_calls:                       0
% 4.07/0.99  smt_fast_solver_calls:                  0
% 4.07/0.99  prop_num_of_clauses:                    7909
% 4.07/0.99  prop_preprocess_simplified:             16138
% 4.07/0.99  prop_fo_subsumed:                       54
% 4.07/0.99  prop_solver_time:                       0.
% 4.07/0.99  smt_solver_time:                        0.
% 4.07/0.99  smt_fast_solver_time:                   0.
% 4.07/0.99  prop_fast_solver_time:                  0.
% 4.07/0.99  prop_unsat_core_time:                   0.
% 4.07/0.99  
% 4.07/0.99  ------ QBF
% 4.07/0.99  
% 4.07/0.99  qbf_q_res:                              0
% 4.07/0.99  qbf_num_tautologies:                    0
% 4.07/0.99  qbf_prep_cycles:                        0
% 4.07/0.99  
% 4.07/0.99  ------ BMC1
% 4.07/0.99  
% 4.07/0.99  bmc1_current_bound:                     -1
% 4.07/0.99  bmc1_last_solved_bound:                 -1
% 4.07/0.99  bmc1_unsat_core_size:                   -1
% 4.07/0.99  bmc1_unsat_core_parents_size:           -1
% 4.07/0.99  bmc1_merge_next_fun:                    0
% 4.07/0.99  bmc1_unsat_core_clauses_time:           0.
% 4.07/0.99  
% 4.07/0.99  ------ Instantiation
% 4.07/0.99  
% 4.07/0.99  inst_num_of_clauses:                    1753
% 4.07/0.99  inst_num_in_passive:                    870
% 4.07/0.99  inst_num_in_active:                     808
% 4.07/0.99  inst_num_in_unprocessed:                75
% 4.07/0.99  inst_num_of_loops:                      1020
% 4.07/0.99  inst_num_of_learning_restarts:          0
% 4.07/0.99  inst_num_moves_active_passive:          207
% 4.07/0.99  inst_lit_activity:                      0
% 4.07/0.99  inst_lit_activity_moves:                0
% 4.07/0.99  inst_num_tautologies:                   0
% 4.07/0.99  inst_num_prop_implied:                  0
% 4.07/0.99  inst_num_existing_simplified:           0
% 4.07/0.99  inst_num_eq_res_simplified:             0
% 4.07/0.99  inst_num_child_elim:                    0
% 4.07/0.99  inst_num_of_dismatching_blockings:      1040
% 4.07/0.99  inst_num_of_non_proper_insts:           2106
% 4.07/0.99  inst_num_of_duplicates:                 0
% 4.07/0.99  inst_inst_num_from_inst_to_res:         0
% 4.07/0.99  inst_dismatching_checking_time:         0.
% 4.07/0.99  
% 4.07/0.99  ------ Resolution
% 4.07/0.99  
% 4.07/0.99  res_num_of_clauses:                     0
% 4.07/0.99  res_num_in_passive:                     0
% 4.07/0.99  res_num_in_active:                      0
% 4.07/0.99  res_num_of_loops:                       156
% 4.07/0.99  res_forward_subset_subsumed:            41
% 4.07/0.99  res_backward_subset_subsumed:           0
% 4.07/0.99  res_forward_subsumed:                   0
% 4.07/0.99  res_backward_subsumed:                  0
% 4.07/0.99  res_forward_subsumption_resolution:     0
% 4.07/0.99  res_backward_subsumption_resolution:    2
% 4.07/0.99  res_clause_to_clause_subsumption:       3098
% 4.07/0.99  res_orphan_elimination:                 0
% 4.07/0.99  res_tautology_del:                      77
% 4.07/0.99  res_num_eq_res_simplified:              0
% 4.07/0.99  res_num_sel_changes:                    0
% 4.07/0.99  res_moves_from_active_to_pass:          0
% 4.07/0.99  
% 4.07/0.99  ------ Superposition
% 4.07/0.99  
% 4.07/0.99  sup_time_total:                         0.
% 4.07/0.99  sup_time_generating:                    0.
% 4.07/0.99  sup_time_sim_full:                      0.
% 4.07/0.99  sup_time_sim_immed:                     0.
% 4.07/0.99  
% 4.07/0.99  sup_num_of_clauses:                     646
% 4.07/0.99  sup_num_in_active:                      183
% 4.07/0.99  sup_num_in_passive:                     463
% 4.07/0.99  sup_num_of_loops:                       202
% 4.07/0.99  sup_fw_superposition:                   698
% 4.07/0.99  sup_bw_superposition:                   943
% 4.07/0.99  sup_immediate_simplified:               671
% 4.07/0.99  sup_given_eliminated:                   0
% 4.07/0.99  comparisons_done:                       0
% 4.07/0.99  comparisons_avoided:                    0
% 4.07/0.99  
% 4.07/0.99  ------ Simplifications
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  sim_fw_subset_subsumed:                 200
% 4.07/0.99  sim_bw_subset_subsumed:                 38
% 4.07/0.99  sim_fw_subsumed:                        442
% 4.07/0.99  sim_bw_subsumed:                        22
% 4.07/0.99  sim_fw_subsumption_res:                 0
% 4.07/0.99  sim_bw_subsumption_res:                 0
% 4.07/0.99  sim_tautology_del:                      159
% 4.07/0.99  sim_eq_tautology_del:                   19
% 4.07/0.99  sim_eq_res_simp:                        91
% 4.07/0.99  sim_fw_demodulated:                     57
% 4.07/0.99  sim_bw_demodulated:                     0
% 4.07/0.99  sim_light_normalised:                   48
% 4.07/0.99  sim_joinable_taut:                      0
% 4.07/0.99  sim_joinable_simp:                      0
% 4.07/0.99  sim_ac_normalised:                      0
% 4.07/0.99  sim_smt_subsumption:                    0
% 4.07/0.99  
%------------------------------------------------------------------------------
