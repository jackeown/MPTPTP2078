%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:57 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 915 expanded)
%              Number of clauses        :  104 ( 257 expanded)
%              Number of leaves         :   24 ( 257 expanded)
%              Depth                    :   24
%              Number of atoms          :  752 (6577 expanded)
%              Number of equality atoms :  180 ( 285 expanded)
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

fof(f14,plain,(
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

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f37])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f84,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f15,plain,(
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
    inference(pure_predicate_removal,[],[f13])).

fof(f16,plain,(
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
    inference(pure_predicate_removal,[],[f15])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,
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

fof(f54,plain,
    ( ( r1_tsep_1(sK10,sK9)
      | r1_tsep_1(sK9,sK10) )
    & ( ~ r1_tsep_1(sK10,sK8)
      | ~ r1_tsep_1(sK8,sK10) )
    & m1_pre_topc(sK8,sK9)
    & m1_pre_topc(sK10,sK7)
    & m1_pre_topc(sK9,sK7)
    & m1_pre_topc(sK8,sK7)
    & l1_pre_topc(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f28,f53,f52,f51,f50])).

fof(f90,plain,(
    m1_pre_topc(sK9,sK7) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f54])).

fof(f7,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f29,plain,(
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

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f21,f30,f29])).

fof(f82,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f70,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f92,plain,(
    m1_pre_topc(sK8,sK9) ),
    inference(cnf_transformation,[],[f54])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f47,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK5(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f44,f47,f46,f45])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f99,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f57])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f83,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f69,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f91,plain,(
    m1_pre_topc(sK10,sK7) ),
    inference(cnf_transformation,[],[f54])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f94,plain,
    ( r1_tsep_1(sK10,sK9)
    | r1_tsep_1(sK9,sK10) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f93,plain,
    ( ~ r1_tsep_1(sK10,sK8)
    | ~ r1_tsep_1(sK8,sK10) ),
    inference(cnf_transformation,[],[f54])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3604,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_29,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_37,negated_conjecture,
    ( m1_pre_topc(sK9,sK7) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_631,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK7 != X0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_37])).

cnf(c_632,plain,
    ( ~ l1_pre_topc(sK7)
    | l1_pre_topc(sK9) ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_39,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_634,plain,
    ( l1_pre_topc(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_632,c_39])).

cnf(c_27,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_16,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_431,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_27,c_16])).

cnf(c_435,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X0,X1)
    | sP0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_431,c_29])).

cnf(c_436,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_435])).

cnf(c_35,negated_conjecture,
    ( m1_pre_topc(sK8,sK9) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_578,plain,
    ( sP0(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK8 != X0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_436,c_35])).

cnf(c_579,plain,
    ( sP0(sK8,sK9)
    | ~ l1_pre_topc(sK9) ),
    inference(unflattening,[status(thm)],[c_578])).

cnf(c_641,plain,
    ( sP0(sK8,sK9) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_634,c_579])).

cnf(c_3581,plain,
    ( sP0(sK8,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_26,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3589,plain,
    ( sP0(X0,X1) != iProver_top
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3600,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3601,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3603,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4575,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(k2_xboole_0(X0,X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3601,c_3603])).

cnf(c_4981,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3600,c_4575])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_106,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5134,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4981,c_106])).

cnf(c_5143,plain,
    ( k2_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X0)
    | sP0(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3589,c_5134])).

cnf(c_5388,plain,
    ( k2_xboole_0(k2_struct_0(sK9),k2_struct_0(sK8)) = k2_struct_0(sK9) ),
    inference(superposition,[status(thm)],[c_3581,c_5143])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3609,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6802,plain,
    ( r2_hidden(X0,k2_struct_0(sK8)) != iProver_top
    | r2_hidden(X0,k2_struct_0(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5388,c_3609])).

cnf(c_9888,plain,
    ( r1_xboole_0(k2_struct_0(sK8),X0) = iProver_top
    | r2_hidden(sK3(k2_struct_0(sK8),X0),k2_struct_0(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3604,c_6802])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK3(X0,X1),X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3605,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_28,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_687,plain,
    ( l1_struct_0(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_634])).

cnf(c_688,plain,
    ( l1_struct_0(sK9) ),
    inference(unflattening,[status(thm)],[c_687])).

cnf(c_3577,plain,
    ( l1_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_688])).

cnf(c_14,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3599,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4067,plain,
    ( u1_struct_0(sK9) = k2_struct_0(sK9) ),
    inference(superposition,[status(thm)],[c_3577,c_3599])).

cnf(c_36,negated_conjecture,
    ( m1_pre_topc(sK10,sK7) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_609,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK7 != X0
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_36])).

cnf(c_610,plain,
    ( ~ l1_pre_topc(sK7)
    | l1_pre_topc(sK10) ),
    inference(unflattening,[status(thm)],[c_609])).

cnf(c_612,plain,
    ( l1_pre_topc(sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_610,c_39])).

cnf(c_680,plain,
    ( l1_struct_0(X0)
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_612])).

cnf(c_681,plain,
    ( l1_struct_0(sK10) ),
    inference(unflattening,[status(thm)],[c_680])).

cnf(c_3578,plain,
    ( l1_struct_0(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_681])).

cnf(c_4065,plain,
    ( u1_struct_0(sK10) = k2_struct_0(sK10) ),
    inference(superposition,[status(thm)],[c_3578,c_3599])).

cnf(c_31,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3587,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5585,plain,
    ( r1_tsep_1(sK10,X0) != iProver_top
    | r1_xboole_0(k2_struct_0(sK10),u1_struct_0(X0)) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_4065,c_3587])).

cnf(c_40,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_55,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_57,plain,
    ( l1_pre_topc(sK10) != iProver_top
    | l1_struct_0(sK10) = iProver_top ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_611,plain,
    ( l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_610])).

cnf(c_7227,plain,
    ( l1_struct_0(X0) != iProver_top
    | r1_xboole_0(k2_struct_0(sK10),u1_struct_0(X0)) = iProver_top
    | r1_tsep_1(sK10,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5585,c_40,c_57,c_611])).

cnf(c_7228,plain,
    ( r1_tsep_1(sK10,X0) != iProver_top
    | r1_xboole_0(k2_struct_0(sK10),u1_struct_0(X0)) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7227])).

cnf(c_7236,plain,
    ( r1_tsep_1(sK10,sK9) != iProver_top
    | r1_xboole_0(k2_struct_0(sK10),k2_struct_0(sK9)) = iProver_top
    | l1_struct_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_4067,c_7228])).

cnf(c_689,plain,
    ( l1_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_688])).

cnf(c_33,negated_conjecture,
    ( r1_tsep_1(sK9,sK10)
    | r1_tsep_1(sK10,sK9) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3585,plain,
    ( r1_tsep_1(sK9,sK10) = iProver_top
    | r1_tsep_1(sK10,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3586,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_tsep_1(X1,X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4426,plain,
    ( r1_tsep_1(sK10,sK9) = iProver_top
    | l1_struct_0(sK9) != iProver_top
    | l1_struct_0(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_3585,c_3586])).

cnf(c_11809,plain,
    ( r1_xboole_0(k2_struct_0(sK10),k2_struct_0(sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7236,c_40,c_57,c_611,c_689,c_4426])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3606,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11814,plain,
    ( r2_hidden(X0,k2_struct_0(sK9)) != iProver_top
    | r2_hidden(X0,k2_struct_0(sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11809,c_3606])).

cnf(c_12044,plain,
    ( r1_xboole_0(X0,k2_struct_0(sK10)) = iProver_top
    | r2_hidden(sK3(X0,k2_struct_0(sK10)),k2_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3605,c_11814])).

cnf(c_16159,plain,
    ( r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9888,c_12044])).

cnf(c_588,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK8 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_35])).

cnf(c_589,plain,
    ( l1_pre_topc(sK8)
    | ~ l1_pre_topc(sK9) ),
    inference(unflattening,[status(thm)],[c_588])).

cnf(c_642,plain,
    ( l1_pre_topc(sK8) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_634,c_589])).

cnf(c_694,plain,
    ( l1_struct_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_642])).

cnf(c_695,plain,
    ( l1_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_3576,plain,
    ( l1_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_695])).

cnf(c_4068,plain,
    ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(superposition,[status(thm)],[c_3576,c_3599])).

cnf(c_5586,plain,
    ( r1_tsep_1(sK8,X0) != iProver_top
    | r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X0)) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4068,c_3587])).

cnf(c_696,plain,
    ( l1_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_695])).

cnf(c_8563,plain,
    ( l1_struct_0(X0) != iProver_top
    | r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X0)) = iProver_top
    | r1_tsep_1(sK8,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5586,c_696])).

cnf(c_8564,plain,
    ( r1_tsep_1(sK8,X0) != iProver_top
    | r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X0)) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8563])).

cnf(c_8572,plain,
    ( r1_tsep_1(sK8,sK10) != iProver_top
    | r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK10)) = iProver_top
    | l1_struct_0(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_4065,c_8564])).

cnf(c_34,negated_conjecture,
    ( ~ r1_tsep_1(sK8,sK10)
    | ~ r1_tsep_1(sK10,sK8) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_45,plain,
    ( r1_tsep_1(sK8,sK10) != iProver_top
    | r1_tsep_1(sK10,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4042,plain,
    ( ~ r1_tsep_1(sK8,sK10)
    | r1_tsep_1(sK10,sK8)
    | ~ l1_struct_0(sK8)
    | ~ l1_struct_0(sK10) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_4043,plain,
    ( r1_tsep_1(sK8,sK10) != iProver_top
    | r1_tsep_1(sK10,sK8) = iProver_top
    | l1_struct_0(sK8) != iProver_top
    | l1_struct_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4042])).

cnf(c_13482,plain,
    ( r1_tsep_1(sK8,sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8572,c_40,c_45,c_57,c_611,c_696,c_4043])).

cnf(c_2932,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4030,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10))
    | u1_struct_0(sK8) != X0
    | u1_struct_0(sK10) != X1 ),
    inference(instantiation,[status(thm)],[c_2932])).

cnf(c_4189,plain,
    ( r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10))
    | ~ r1_xboole_0(k2_struct_0(sK8),X0)
    | u1_struct_0(sK8) != k2_struct_0(sK8)
    | u1_struct_0(sK10) != X0 ),
    inference(instantiation,[status(thm)],[c_4030])).

cnf(c_4508,plain,
    ( r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10))
    | ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK10))
    | u1_struct_0(sK8) != k2_struct_0(sK8)
    | u1_struct_0(sK10) != k2_struct_0(sK10) ),
    inference(instantiation,[status(thm)],[c_4189])).

cnf(c_4510,plain,
    ( u1_struct_0(sK8) != k2_struct_0(sK8)
    | u1_struct_0(sK10) != k2_struct_0(sK10)
    | r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10)) = iProver_top
    | r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4508])).

cnf(c_30,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3896,plain,
    ( r1_tsep_1(sK8,sK10)
    | ~ r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10))
    | ~ l1_struct_0(sK8)
    | ~ l1_struct_0(sK10) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_3897,plain,
    ( r1_tsep_1(sK8,sK10) = iProver_top
    | r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10)) != iProver_top
    | l1_struct_0(sK8) != iProver_top
    | l1_struct_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3896])).

cnf(c_98,plain,
    ( ~ l1_struct_0(sK10)
    | u1_struct_0(sK10) = k2_struct_0(sK10) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_56,plain,
    ( ~ l1_pre_topc(sK10)
    | l1_struct_0(sK10) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16159,c_13482,c_4510,c_4068,c_3897,c_696,c_611,c_610,c_98,c_57,c_56,c_40,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:07:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.71/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.71/1.00  
% 3.71/1.00  ------  iProver source info
% 3.71/1.00  
% 3.71/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.71/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.71/1.00  git: non_committed_changes: false
% 3.71/1.00  git: last_make_outside_of_git: false
% 3.71/1.00  
% 3.71/1.00  ------ 
% 3.71/1.00  
% 3.71/1.00  ------ Input Options
% 3.71/1.00  
% 3.71/1.00  --out_options                           all
% 3.71/1.00  --tptp_safe_out                         true
% 3.71/1.00  --problem_path                          ""
% 3.71/1.00  --include_path                          ""
% 3.71/1.00  --clausifier                            res/vclausify_rel
% 3.71/1.00  --clausifier_options                    --mode clausify
% 3.71/1.00  --stdin                                 false
% 3.71/1.00  --stats_out                             all
% 3.71/1.00  
% 3.71/1.00  ------ General Options
% 3.71/1.00  
% 3.71/1.00  --fof                                   false
% 3.71/1.00  --time_out_real                         305.
% 3.71/1.00  --time_out_virtual                      -1.
% 3.71/1.00  --symbol_type_check                     false
% 3.71/1.00  --clausify_out                          false
% 3.71/1.00  --sig_cnt_out                           false
% 3.71/1.00  --trig_cnt_out                          false
% 3.71/1.00  --trig_cnt_out_tolerance                1.
% 3.71/1.00  --trig_cnt_out_sk_spl                   false
% 3.71/1.00  --abstr_cl_out                          false
% 3.71/1.00  
% 3.71/1.00  ------ Global Options
% 3.71/1.00  
% 3.71/1.00  --schedule                              default
% 3.71/1.00  --add_important_lit                     false
% 3.71/1.00  --prop_solver_per_cl                    1000
% 3.71/1.00  --min_unsat_core                        false
% 3.71/1.00  --soft_assumptions                      false
% 3.71/1.00  --soft_lemma_size                       3
% 3.71/1.00  --prop_impl_unit_size                   0
% 3.71/1.00  --prop_impl_unit                        []
% 3.71/1.00  --share_sel_clauses                     true
% 3.71/1.00  --reset_solvers                         false
% 3.71/1.00  --bc_imp_inh                            [conj_cone]
% 3.71/1.00  --conj_cone_tolerance                   3.
% 3.71/1.00  --extra_neg_conj                        none
% 3.71/1.00  --large_theory_mode                     true
% 3.71/1.00  --prolific_symb_bound                   200
% 3.71/1.00  --lt_threshold                          2000
% 3.71/1.00  --clause_weak_htbl                      true
% 3.71/1.00  --gc_record_bc_elim                     false
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing Options
% 3.71/1.00  
% 3.71/1.00  --preprocessing_flag                    true
% 3.71/1.00  --time_out_prep_mult                    0.1
% 3.71/1.00  --splitting_mode                        input
% 3.71/1.00  --splitting_grd                         true
% 3.71/1.00  --splitting_cvd                         false
% 3.71/1.00  --splitting_cvd_svl                     false
% 3.71/1.00  --splitting_nvd                         32
% 3.71/1.00  --sub_typing                            true
% 3.71/1.00  --prep_gs_sim                           true
% 3.71/1.00  --prep_unflatten                        true
% 3.71/1.00  --prep_res_sim                          true
% 3.71/1.00  --prep_upred                            true
% 3.71/1.00  --prep_sem_filter                       exhaustive
% 3.71/1.00  --prep_sem_filter_out                   false
% 3.71/1.00  --pred_elim                             true
% 3.71/1.00  --res_sim_input                         true
% 3.71/1.00  --eq_ax_congr_red                       true
% 3.71/1.00  --pure_diseq_elim                       true
% 3.71/1.00  --brand_transform                       false
% 3.71/1.00  --non_eq_to_eq                          false
% 3.71/1.00  --prep_def_merge                        true
% 3.71/1.00  --prep_def_merge_prop_impl              false
% 3.71/1.00  --prep_def_merge_mbd                    true
% 3.71/1.00  --prep_def_merge_tr_red                 false
% 3.71/1.00  --prep_def_merge_tr_cl                  false
% 3.71/1.00  --smt_preprocessing                     true
% 3.71/1.00  --smt_ac_axioms                         fast
% 3.71/1.00  --preprocessed_out                      false
% 3.71/1.00  --preprocessed_stats                    false
% 3.71/1.00  
% 3.71/1.00  ------ Abstraction refinement Options
% 3.71/1.00  
% 3.71/1.00  --abstr_ref                             []
% 3.71/1.00  --abstr_ref_prep                        false
% 3.71/1.00  --abstr_ref_until_sat                   false
% 3.71/1.00  --abstr_ref_sig_restrict                funpre
% 3.71/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/1.00  --abstr_ref_under                       []
% 3.71/1.00  
% 3.71/1.00  ------ SAT Options
% 3.71/1.00  
% 3.71/1.00  --sat_mode                              false
% 3.71/1.00  --sat_fm_restart_options                ""
% 3.71/1.00  --sat_gr_def                            false
% 3.71/1.00  --sat_epr_types                         true
% 3.71/1.00  --sat_non_cyclic_types                  false
% 3.71/1.00  --sat_finite_models                     false
% 3.71/1.00  --sat_fm_lemmas                         false
% 3.71/1.00  --sat_fm_prep                           false
% 3.71/1.00  --sat_fm_uc_incr                        true
% 3.71/1.00  --sat_out_model                         small
% 3.71/1.00  --sat_out_clauses                       false
% 3.71/1.00  
% 3.71/1.00  ------ QBF Options
% 3.71/1.00  
% 3.71/1.00  --qbf_mode                              false
% 3.71/1.00  --qbf_elim_univ                         false
% 3.71/1.00  --qbf_dom_inst                          none
% 3.71/1.00  --qbf_dom_pre_inst                      false
% 3.71/1.00  --qbf_sk_in                             false
% 3.71/1.00  --qbf_pred_elim                         true
% 3.71/1.00  --qbf_split                             512
% 3.71/1.00  
% 3.71/1.00  ------ BMC1 Options
% 3.71/1.00  
% 3.71/1.00  --bmc1_incremental                      false
% 3.71/1.00  --bmc1_axioms                           reachable_all
% 3.71/1.00  --bmc1_min_bound                        0
% 3.71/1.00  --bmc1_max_bound                        -1
% 3.71/1.00  --bmc1_max_bound_default                -1
% 3.71/1.00  --bmc1_symbol_reachability              true
% 3.71/1.00  --bmc1_property_lemmas                  false
% 3.71/1.00  --bmc1_k_induction                      false
% 3.71/1.00  --bmc1_non_equiv_states                 false
% 3.71/1.00  --bmc1_deadlock                         false
% 3.71/1.00  --bmc1_ucm                              false
% 3.71/1.00  --bmc1_add_unsat_core                   none
% 3.71/1.00  --bmc1_unsat_core_children              false
% 3.71/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/1.00  --bmc1_out_stat                         full
% 3.71/1.00  --bmc1_ground_init                      false
% 3.71/1.00  --bmc1_pre_inst_next_state              false
% 3.71/1.00  --bmc1_pre_inst_state                   false
% 3.71/1.00  --bmc1_pre_inst_reach_state             false
% 3.71/1.00  --bmc1_out_unsat_core                   false
% 3.71/1.00  --bmc1_aig_witness_out                  false
% 3.71/1.00  --bmc1_verbose                          false
% 3.71/1.00  --bmc1_dump_clauses_tptp                false
% 3.71/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.71/1.00  --bmc1_dump_file                        -
% 3.71/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.71/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.71/1.00  --bmc1_ucm_extend_mode                  1
% 3.71/1.00  --bmc1_ucm_init_mode                    2
% 3.71/1.00  --bmc1_ucm_cone_mode                    none
% 3.71/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.71/1.00  --bmc1_ucm_relax_model                  4
% 3.71/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.71/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/1.00  --bmc1_ucm_layered_model                none
% 3.71/1.00  --bmc1_ucm_max_lemma_size               10
% 3.71/1.00  
% 3.71/1.00  ------ AIG Options
% 3.71/1.00  
% 3.71/1.00  --aig_mode                              false
% 3.71/1.00  
% 3.71/1.00  ------ Instantiation Options
% 3.71/1.00  
% 3.71/1.00  --instantiation_flag                    true
% 3.71/1.00  --inst_sos_flag                         false
% 3.71/1.00  --inst_sos_phase                        true
% 3.71/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/1.00  --inst_lit_sel_side                     num_symb
% 3.71/1.00  --inst_solver_per_active                1400
% 3.71/1.00  --inst_solver_calls_frac                1.
% 3.71/1.00  --inst_passive_queue_type               priority_queues
% 3.71/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/1.00  --inst_passive_queues_freq              [25;2]
% 3.71/1.00  --inst_dismatching                      true
% 3.71/1.00  --inst_eager_unprocessed_to_passive     true
% 3.71/1.00  --inst_prop_sim_given                   true
% 3.71/1.00  --inst_prop_sim_new                     false
% 3.71/1.00  --inst_subs_new                         false
% 3.71/1.00  --inst_eq_res_simp                      false
% 3.71/1.00  --inst_subs_given                       false
% 3.71/1.00  --inst_orphan_elimination               true
% 3.71/1.00  --inst_learning_loop_flag               true
% 3.71/1.00  --inst_learning_start                   3000
% 3.71/1.00  --inst_learning_factor                  2
% 3.71/1.00  --inst_start_prop_sim_after_learn       3
% 3.71/1.00  --inst_sel_renew                        solver
% 3.71/1.00  --inst_lit_activity_flag                true
% 3.71/1.00  --inst_restr_to_given                   false
% 3.71/1.00  --inst_activity_threshold               500
% 3.71/1.00  --inst_out_proof                        true
% 3.71/1.00  
% 3.71/1.00  ------ Resolution Options
% 3.71/1.00  
% 3.71/1.00  --resolution_flag                       true
% 3.71/1.00  --res_lit_sel                           adaptive
% 3.71/1.00  --res_lit_sel_side                      none
% 3.71/1.00  --res_ordering                          kbo
% 3.71/1.00  --res_to_prop_solver                    active
% 3.71/1.00  --res_prop_simpl_new                    false
% 3.71/1.00  --res_prop_simpl_given                  true
% 3.71/1.00  --res_passive_queue_type                priority_queues
% 3.71/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/1.00  --res_passive_queues_freq               [15;5]
% 3.71/1.00  --res_forward_subs                      full
% 3.71/1.00  --res_backward_subs                     full
% 3.71/1.00  --res_forward_subs_resolution           true
% 3.71/1.00  --res_backward_subs_resolution          true
% 3.71/1.00  --res_orphan_elimination                true
% 3.71/1.00  --res_time_limit                        2.
% 3.71/1.00  --res_out_proof                         true
% 3.71/1.00  
% 3.71/1.00  ------ Superposition Options
% 3.71/1.00  
% 3.71/1.00  --superposition_flag                    true
% 3.71/1.00  --sup_passive_queue_type                priority_queues
% 3.71/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.71/1.00  --demod_completeness_check              fast
% 3.71/1.00  --demod_use_ground                      true
% 3.71/1.00  --sup_to_prop_solver                    passive
% 3.71/1.00  --sup_prop_simpl_new                    true
% 3.71/1.00  --sup_prop_simpl_given                  true
% 3.71/1.00  --sup_fun_splitting                     false
% 3.71/1.00  --sup_smt_interval                      50000
% 3.71/1.00  
% 3.71/1.00  ------ Superposition Simplification Setup
% 3.71/1.00  
% 3.71/1.00  --sup_indices_passive                   []
% 3.71/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_full_bw                           [BwDemod]
% 3.71/1.00  --sup_immed_triv                        [TrivRules]
% 3.71/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_immed_bw_main                     []
% 3.71/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/1.00  
% 3.71/1.00  ------ Combination Options
% 3.71/1.00  
% 3.71/1.00  --comb_res_mult                         3
% 3.71/1.00  --comb_sup_mult                         2
% 3.71/1.00  --comb_inst_mult                        10
% 3.71/1.00  
% 3.71/1.00  ------ Debug Options
% 3.71/1.00  
% 3.71/1.00  --dbg_backtrace                         false
% 3.71/1.00  --dbg_dump_prop_clauses                 false
% 3.71/1.00  --dbg_dump_prop_clauses_file            -
% 3.71/1.00  --dbg_out_stat                          false
% 3.71/1.00  ------ Parsing...
% 3.71/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.71/1.00  ------ Proving...
% 3.71/1.00  ------ Problem Properties 
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  clauses                                 37
% 3.71/1.00  conjectures                             2
% 3.71/1.00  EPR                                     14
% 3.71/1.00  Horn                                    28
% 3.71/1.00  unary                                   10
% 3.71/1.00  binary                                  8
% 3.71/1.00  lits                                    98
% 3.71/1.00  lits eq                                 8
% 3.71/1.00  fd_pure                                 0
% 3.71/1.00  fd_pseudo                               0
% 3.71/1.00  fd_cond                                 0
% 3.71/1.00  fd_pseudo_cond                          4
% 3.71/1.00  AC symbols                              0
% 3.71/1.00  
% 3.71/1.00  ------ Schedule dynamic 5 is on 
% 3.71/1.00  
% 3.71/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  ------ 
% 3.71/1.00  Current options:
% 3.71/1.00  ------ 
% 3.71/1.00  
% 3.71/1.00  ------ Input Options
% 3.71/1.00  
% 3.71/1.00  --out_options                           all
% 3.71/1.00  --tptp_safe_out                         true
% 3.71/1.00  --problem_path                          ""
% 3.71/1.00  --include_path                          ""
% 3.71/1.00  --clausifier                            res/vclausify_rel
% 3.71/1.00  --clausifier_options                    --mode clausify
% 3.71/1.00  --stdin                                 false
% 3.71/1.00  --stats_out                             all
% 3.71/1.00  
% 3.71/1.00  ------ General Options
% 3.71/1.00  
% 3.71/1.00  --fof                                   false
% 3.71/1.00  --time_out_real                         305.
% 3.71/1.00  --time_out_virtual                      -1.
% 3.71/1.00  --symbol_type_check                     false
% 3.71/1.00  --clausify_out                          false
% 3.71/1.00  --sig_cnt_out                           false
% 3.71/1.00  --trig_cnt_out                          false
% 3.71/1.00  --trig_cnt_out_tolerance                1.
% 3.71/1.00  --trig_cnt_out_sk_spl                   false
% 3.71/1.00  --abstr_cl_out                          false
% 3.71/1.00  
% 3.71/1.00  ------ Global Options
% 3.71/1.00  
% 3.71/1.00  --schedule                              default
% 3.71/1.00  --add_important_lit                     false
% 3.71/1.00  --prop_solver_per_cl                    1000
% 3.71/1.00  --min_unsat_core                        false
% 3.71/1.00  --soft_assumptions                      false
% 3.71/1.00  --soft_lemma_size                       3
% 3.71/1.00  --prop_impl_unit_size                   0
% 3.71/1.00  --prop_impl_unit                        []
% 3.71/1.00  --share_sel_clauses                     true
% 3.71/1.00  --reset_solvers                         false
% 3.71/1.00  --bc_imp_inh                            [conj_cone]
% 3.71/1.00  --conj_cone_tolerance                   3.
% 3.71/1.00  --extra_neg_conj                        none
% 3.71/1.00  --large_theory_mode                     true
% 3.71/1.00  --prolific_symb_bound                   200
% 3.71/1.00  --lt_threshold                          2000
% 3.71/1.00  --clause_weak_htbl                      true
% 3.71/1.00  --gc_record_bc_elim                     false
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing Options
% 3.71/1.00  
% 3.71/1.00  --preprocessing_flag                    true
% 3.71/1.00  --time_out_prep_mult                    0.1
% 3.71/1.00  --splitting_mode                        input
% 3.71/1.00  --splitting_grd                         true
% 3.71/1.00  --splitting_cvd                         false
% 3.71/1.00  --splitting_cvd_svl                     false
% 3.71/1.00  --splitting_nvd                         32
% 3.71/1.00  --sub_typing                            true
% 3.71/1.00  --prep_gs_sim                           true
% 3.71/1.00  --prep_unflatten                        true
% 3.71/1.00  --prep_res_sim                          true
% 3.71/1.00  --prep_upred                            true
% 3.71/1.00  --prep_sem_filter                       exhaustive
% 3.71/1.00  --prep_sem_filter_out                   false
% 3.71/1.00  --pred_elim                             true
% 3.71/1.00  --res_sim_input                         true
% 3.71/1.00  --eq_ax_congr_red                       true
% 3.71/1.00  --pure_diseq_elim                       true
% 3.71/1.00  --brand_transform                       false
% 3.71/1.00  --non_eq_to_eq                          false
% 3.71/1.00  --prep_def_merge                        true
% 3.71/1.00  --prep_def_merge_prop_impl              false
% 3.71/1.00  --prep_def_merge_mbd                    true
% 3.71/1.00  --prep_def_merge_tr_red                 false
% 3.71/1.00  --prep_def_merge_tr_cl                  false
% 3.71/1.00  --smt_preprocessing                     true
% 3.71/1.00  --smt_ac_axioms                         fast
% 3.71/1.00  --preprocessed_out                      false
% 3.71/1.00  --preprocessed_stats                    false
% 3.71/1.00  
% 3.71/1.00  ------ Abstraction refinement Options
% 3.71/1.00  
% 3.71/1.00  --abstr_ref                             []
% 3.71/1.00  --abstr_ref_prep                        false
% 3.71/1.00  --abstr_ref_until_sat                   false
% 3.71/1.00  --abstr_ref_sig_restrict                funpre
% 3.71/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/1.00  --abstr_ref_under                       []
% 3.71/1.00  
% 3.71/1.00  ------ SAT Options
% 3.71/1.00  
% 3.71/1.00  --sat_mode                              false
% 3.71/1.00  --sat_fm_restart_options                ""
% 3.71/1.00  --sat_gr_def                            false
% 3.71/1.00  --sat_epr_types                         true
% 3.71/1.00  --sat_non_cyclic_types                  false
% 3.71/1.00  --sat_finite_models                     false
% 3.71/1.00  --sat_fm_lemmas                         false
% 3.71/1.00  --sat_fm_prep                           false
% 3.71/1.00  --sat_fm_uc_incr                        true
% 3.71/1.00  --sat_out_model                         small
% 3.71/1.00  --sat_out_clauses                       false
% 3.71/1.00  
% 3.71/1.00  ------ QBF Options
% 3.71/1.00  
% 3.71/1.00  --qbf_mode                              false
% 3.71/1.00  --qbf_elim_univ                         false
% 3.71/1.00  --qbf_dom_inst                          none
% 3.71/1.00  --qbf_dom_pre_inst                      false
% 3.71/1.00  --qbf_sk_in                             false
% 3.71/1.00  --qbf_pred_elim                         true
% 3.71/1.00  --qbf_split                             512
% 3.71/1.00  
% 3.71/1.00  ------ BMC1 Options
% 3.71/1.00  
% 3.71/1.00  --bmc1_incremental                      false
% 3.71/1.00  --bmc1_axioms                           reachable_all
% 3.71/1.00  --bmc1_min_bound                        0
% 3.71/1.00  --bmc1_max_bound                        -1
% 3.71/1.00  --bmc1_max_bound_default                -1
% 3.71/1.00  --bmc1_symbol_reachability              true
% 3.71/1.00  --bmc1_property_lemmas                  false
% 3.71/1.00  --bmc1_k_induction                      false
% 3.71/1.00  --bmc1_non_equiv_states                 false
% 3.71/1.00  --bmc1_deadlock                         false
% 3.71/1.00  --bmc1_ucm                              false
% 3.71/1.00  --bmc1_add_unsat_core                   none
% 3.71/1.00  --bmc1_unsat_core_children              false
% 3.71/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/1.00  --bmc1_out_stat                         full
% 3.71/1.00  --bmc1_ground_init                      false
% 3.71/1.00  --bmc1_pre_inst_next_state              false
% 3.71/1.00  --bmc1_pre_inst_state                   false
% 3.71/1.00  --bmc1_pre_inst_reach_state             false
% 3.71/1.00  --bmc1_out_unsat_core                   false
% 3.71/1.00  --bmc1_aig_witness_out                  false
% 3.71/1.00  --bmc1_verbose                          false
% 3.71/1.00  --bmc1_dump_clauses_tptp                false
% 3.71/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.71/1.00  --bmc1_dump_file                        -
% 3.71/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.71/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.71/1.00  --bmc1_ucm_extend_mode                  1
% 3.71/1.00  --bmc1_ucm_init_mode                    2
% 3.71/1.00  --bmc1_ucm_cone_mode                    none
% 3.71/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.71/1.00  --bmc1_ucm_relax_model                  4
% 3.71/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.71/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/1.00  --bmc1_ucm_layered_model                none
% 3.71/1.00  --bmc1_ucm_max_lemma_size               10
% 3.71/1.00  
% 3.71/1.00  ------ AIG Options
% 3.71/1.00  
% 3.71/1.00  --aig_mode                              false
% 3.71/1.00  
% 3.71/1.00  ------ Instantiation Options
% 3.71/1.00  
% 3.71/1.00  --instantiation_flag                    true
% 3.71/1.00  --inst_sos_flag                         false
% 3.71/1.00  --inst_sos_phase                        true
% 3.71/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/1.00  --inst_lit_sel_side                     none
% 3.71/1.00  --inst_solver_per_active                1400
% 3.71/1.00  --inst_solver_calls_frac                1.
% 3.71/1.00  --inst_passive_queue_type               priority_queues
% 3.71/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/1.00  --inst_passive_queues_freq              [25;2]
% 3.71/1.00  --inst_dismatching                      true
% 3.71/1.00  --inst_eager_unprocessed_to_passive     true
% 3.71/1.00  --inst_prop_sim_given                   true
% 3.71/1.00  --inst_prop_sim_new                     false
% 3.71/1.00  --inst_subs_new                         false
% 3.71/1.00  --inst_eq_res_simp                      false
% 3.71/1.00  --inst_subs_given                       false
% 3.71/1.00  --inst_orphan_elimination               true
% 3.71/1.00  --inst_learning_loop_flag               true
% 3.71/1.00  --inst_learning_start                   3000
% 3.71/1.00  --inst_learning_factor                  2
% 3.71/1.00  --inst_start_prop_sim_after_learn       3
% 3.71/1.00  --inst_sel_renew                        solver
% 3.71/1.00  --inst_lit_activity_flag                true
% 3.71/1.00  --inst_restr_to_given                   false
% 3.71/1.00  --inst_activity_threshold               500
% 3.71/1.00  --inst_out_proof                        true
% 3.71/1.00  
% 3.71/1.00  ------ Resolution Options
% 3.71/1.00  
% 3.71/1.00  --resolution_flag                       false
% 3.71/1.00  --res_lit_sel                           adaptive
% 3.71/1.00  --res_lit_sel_side                      none
% 3.71/1.00  --res_ordering                          kbo
% 3.71/1.00  --res_to_prop_solver                    active
% 3.71/1.00  --res_prop_simpl_new                    false
% 3.71/1.00  --res_prop_simpl_given                  true
% 3.71/1.00  --res_passive_queue_type                priority_queues
% 3.71/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/1.00  --res_passive_queues_freq               [15;5]
% 3.71/1.00  --res_forward_subs                      full
% 3.71/1.00  --res_backward_subs                     full
% 3.71/1.00  --res_forward_subs_resolution           true
% 3.71/1.00  --res_backward_subs_resolution          true
% 3.71/1.00  --res_orphan_elimination                true
% 3.71/1.00  --res_time_limit                        2.
% 3.71/1.00  --res_out_proof                         true
% 3.71/1.00  
% 3.71/1.00  ------ Superposition Options
% 3.71/1.00  
% 3.71/1.00  --superposition_flag                    true
% 3.71/1.00  --sup_passive_queue_type                priority_queues
% 3.71/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.71/1.00  --demod_completeness_check              fast
% 3.71/1.00  --demod_use_ground                      true
% 3.71/1.00  --sup_to_prop_solver                    passive
% 3.71/1.00  --sup_prop_simpl_new                    true
% 3.71/1.00  --sup_prop_simpl_given                  true
% 3.71/1.00  --sup_fun_splitting                     false
% 3.71/1.00  --sup_smt_interval                      50000
% 3.71/1.00  
% 3.71/1.00  ------ Superposition Simplification Setup
% 3.71/1.00  
% 3.71/1.00  --sup_indices_passive                   []
% 3.71/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_full_bw                           [BwDemod]
% 3.71/1.00  --sup_immed_triv                        [TrivRules]
% 3.71/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_immed_bw_main                     []
% 3.71/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/1.00  
% 3.71/1.00  ------ Combination Options
% 3.71/1.00  
% 3.71/1.00  --comb_res_mult                         3
% 3.71/1.00  --comb_sup_mult                         2
% 3.71/1.00  --comb_inst_mult                        10
% 3.71/1.00  
% 3.71/1.00  ------ Debug Options
% 3.71/1.00  
% 3.71/1.00  --dbg_backtrace                         false
% 3.71/1.00  --dbg_dump_prop_clauses                 false
% 3.71/1.00  --dbg_dump_prop_clauses_file            -
% 3.71/1.00  --dbg_out_stat                          false
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  ------ Proving...
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  % SZS status Theorem for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  fof(f2,axiom,(
% 3.71/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f14,plain,(
% 3.71/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.71/1.00    inference(rectify,[],[f2])).
% 3.71/1.00  
% 3.71/1.00  fof(f17,plain,(
% 3.71/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.71/1.00    inference(ennf_transformation,[],[f14])).
% 3.71/1.00  
% 3.71/1.00  fof(f37,plain,(
% 3.71/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f38,plain,(
% 3.71/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.71/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f37])).
% 3.71/1.00  
% 3.71/1.00  fof(f61,plain,(
% 3.71/1.00    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f38])).
% 3.71/1.00  
% 3.71/1.00  fof(f9,axiom,(
% 3.71/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f23,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.71/1.00    inference(ennf_transformation,[],[f9])).
% 3.71/1.00  
% 3.71/1.00  fof(f84,plain,(
% 3.71/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f23])).
% 3.71/1.00  
% 3.71/1.00  fof(f12,conjecture,(
% 3.71/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 3.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f13,negated_conjecture,(
% 3.71/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 3.71/1.00    inference(negated_conjecture,[],[f12])).
% 3.71/1.00  
% 3.71/1.00  fof(f15,plain,(
% 3.71/1.00    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 3.71/1.00    inference(pure_predicate_removal,[],[f13])).
% 3.71/1.00  
% 3.71/1.00  fof(f16,plain,(
% 3.71/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 3.71/1.00    inference(pure_predicate_removal,[],[f15])).
% 3.71/1.00  
% 3.71/1.00  fof(f27,plain,(
% 3.71/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 3.71/1.00    inference(ennf_transformation,[],[f16])).
% 3.71/1.00  
% 3.71/1.00  fof(f28,plain,(
% 3.71/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 3.71/1.00    inference(flattening,[],[f27])).
% 3.71/1.00  
% 3.71/1.00  fof(f53,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) => ((r1_tsep_1(sK10,X2) | r1_tsep_1(X2,sK10)) & (~r1_tsep_1(sK10,X1) | ~r1_tsep_1(X1,sK10)) & m1_pre_topc(X1,X2) & m1_pre_topc(sK10,X0))) )),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f52,plain,(
% 3.71/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) => (? [X3] : ((r1_tsep_1(X3,sK9) | r1_tsep_1(sK9,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,sK9) & m1_pre_topc(X3,X0)) & m1_pre_topc(sK9,X0))) )),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f51,plain,(
% 3.71/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) => (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK8) | ~r1_tsep_1(sK8,X3)) & m1_pre_topc(sK8,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(sK8,X0))) )),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f50,plain,(
% 3.71/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK7)) & m1_pre_topc(X2,sK7)) & m1_pre_topc(X1,sK7)) & l1_pre_topc(sK7))),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f54,plain,(
% 3.71/1.00    ((((r1_tsep_1(sK10,sK9) | r1_tsep_1(sK9,sK10)) & (~r1_tsep_1(sK10,sK8) | ~r1_tsep_1(sK8,sK10)) & m1_pre_topc(sK8,sK9) & m1_pre_topc(sK10,sK7)) & m1_pre_topc(sK9,sK7)) & m1_pre_topc(sK8,sK7)) & l1_pre_topc(sK7)),
% 3.71/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f28,f53,f52,f51,f50])).
% 3.71/1.00  
% 3.71/1.00  fof(f90,plain,(
% 3.71/1.00    m1_pre_topc(sK9,sK7)),
% 3.71/1.00    inference(cnf_transformation,[],[f54])).
% 3.71/1.00  
% 3.71/1.00  fof(f88,plain,(
% 3.71/1.00    l1_pre_topc(sK7)),
% 3.71/1.00    inference(cnf_transformation,[],[f54])).
% 3.71/1.00  
% 3.71/1.00  fof(f7,axiom,(
% 3.71/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 3.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f21,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.71/1.00    inference(ennf_transformation,[],[f7])).
% 3.71/1.00  
% 3.71/1.00  fof(f30,plain,(
% 3.71/1.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 3.71/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.71/1.00  
% 3.71/1.00  fof(f29,plain,(
% 3.71/1.00    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 3.71/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.71/1.00  
% 3.71/1.00  fof(f31,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.71/1.00    inference(definition_folding,[],[f21,f30,f29])).
% 3.71/1.00  
% 3.71/1.00  fof(f82,plain,(
% 3.71/1.00    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f31])).
% 3.71/1.00  
% 3.71/1.00  fof(f41,plain,(
% 3.71/1.00    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 3.71/1.00    inference(nnf_transformation,[],[f30])).
% 3.71/1.00  
% 3.71/1.00  fof(f70,plain,(
% 3.71/1.00    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f41])).
% 3.71/1.00  
% 3.71/1.00  fof(f92,plain,(
% 3.71/1.00    m1_pre_topc(sK8,sK9)),
% 3.71/1.00    inference(cnf_transformation,[],[f54])).
% 3.71/1.00  
% 3.71/1.00  fof(f42,plain,(
% 3.71/1.00    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 3.71/1.00    inference(nnf_transformation,[],[f29])).
% 3.71/1.00  
% 3.71/1.00  fof(f43,plain,(
% 3.71/1.00    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 3.71/1.00    inference(flattening,[],[f42])).
% 3.71/1.00  
% 3.71/1.00  fof(f44,plain,(
% 3.71/1.00    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 3.71/1.00    inference(rectify,[],[f43])).
% 3.71/1.00  
% 3.71/1.00  fof(f47,plain,(
% 3.71/1.00    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f46,plain,(
% 3.71/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK5(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f45,plain,(
% 3.71/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK4(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK4(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK4(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f48,plain,(
% 3.71/1.00    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK4(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0)) = sK4(X0,X1) & r2_hidden(sK5(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK4(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 3.71/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f44,f47,f46,f45])).
% 3.71/1.00  
% 3.71/1.00  fof(f72,plain,(
% 3.71/1.00    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f48])).
% 3.71/1.00  
% 3.71/1.00  fof(f5,axiom,(
% 3.71/1.00    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f18,plain,(
% 3.71/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.71/1.00    inference(ennf_transformation,[],[f5])).
% 3.71/1.00  
% 3.71/1.00  fof(f19,plain,(
% 3.71/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.71/1.00    inference(flattening,[],[f18])).
% 3.71/1.00  
% 3.71/1.00  fof(f68,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f19])).
% 3.71/1.00  
% 3.71/1.00  fof(f4,axiom,(
% 3.71/1.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f67,plain,(
% 3.71/1.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.71/1.00    inference(cnf_transformation,[],[f4])).
% 3.71/1.00  
% 3.71/1.00  fof(f3,axiom,(
% 3.71/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f39,plain,(
% 3.71/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.71/1.00    inference(nnf_transformation,[],[f3])).
% 3.71/1.00  
% 3.71/1.00  fof(f40,plain,(
% 3.71/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.71/1.00    inference(flattening,[],[f39])).
% 3.71/1.00  
% 3.71/1.00  fof(f66,plain,(
% 3.71/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f40])).
% 3.71/1.00  
% 3.71/1.00  fof(f64,plain,(
% 3.71/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.71/1.00    inference(cnf_transformation,[],[f40])).
% 3.71/1.00  
% 3.71/1.00  fof(f99,plain,(
% 3.71/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.71/1.00    inference(equality_resolution,[],[f64])).
% 3.71/1.00  
% 3.71/1.00  fof(f1,axiom,(
% 3.71/1.00    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f32,plain,(
% 3.71/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.71/1.00    inference(nnf_transformation,[],[f1])).
% 3.71/1.00  
% 3.71/1.00  fof(f33,plain,(
% 3.71/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.71/1.00    inference(flattening,[],[f32])).
% 3.71/1.00  
% 3.71/1.00  fof(f34,plain,(
% 3.71/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.71/1.00    inference(rectify,[],[f33])).
% 3.71/1.00  
% 3.71/1.00  fof(f35,plain,(
% 3.71/1.00    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f36,plain,(
% 3.71/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.71/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 3.71/1.00  
% 3.71/1.00  fof(f57,plain,(
% 3.71/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.71/1.00    inference(cnf_transformation,[],[f36])).
% 3.71/1.00  
% 3.71/1.00  fof(f95,plain,(
% 3.71/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 3.71/1.00    inference(equality_resolution,[],[f57])).
% 3.71/1.00  
% 3.71/1.00  fof(f62,plain,(
% 3.71/1.00    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f38])).
% 3.71/1.00  
% 3.71/1.00  fof(f8,axiom,(
% 3.71/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f22,plain,(
% 3.71/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.71/1.00    inference(ennf_transformation,[],[f8])).
% 3.71/1.00  
% 3.71/1.00  fof(f83,plain,(
% 3.71/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f22])).
% 3.71/1.00  
% 3.71/1.00  fof(f6,axiom,(
% 3.71/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f20,plain,(
% 3.71/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.71/1.00    inference(ennf_transformation,[],[f6])).
% 3.71/1.00  
% 3.71/1.00  fof(f69,plain,(
% 3.71/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f20])).
% 3.71/1.00  
% 3.71/1.00  fof(f91,plain,(
% 3.71/1.00    m1_pre_topc(sK10,sK7)),
% 3.71/1.00    inference(cnf_transformation,[],[f54])).
% 3.71/1.00  
% 3.71/1.00  fof(f10,axiom,(
% 3.71/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 3.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f24,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.71/1.00    inference(ennf_transformation,[],[f10])).
% 3.71/1.00  
% 3.71/1.00  fof(f49,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.71/1.00    inference(nnf_transformation,[],[f24])).
% 3.71/1.00  
% 3.71/1.00  fof(f85,plain,(
% 3.71/1.00    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f49])).
% 3.71/1.00  
% 3.71/1.00  fof(f94,plain,(
% 3.71/1.00    r1_tsep_1(sK10,sK9) | r1_tsep_1(sK9,sK10)),
% 3.71/1.00    inference(cnf_transformation,[],[f54])).
% 3.71/1.00  
% 3.71/1.00  fof(f11,axiom,(
% 3.71/1.00    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 3.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f25,plain,(
% 3.71/1.00    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 3.71/1.00    inference(ennf_transformation,[],[f11])).
% 3.71/1.00  
% 3.71/1.00  fof(f26,plain,(
% 3.71/1.00    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 3.71/1.00    inference(flattening,[],[f25])).
% 3.71/1.00  
% 3.71/1.00  fof(f87,plain,(
% 3.71/1.00    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f26])).
% 3.71/1.00  
% 3.71/1.00  fof(f63,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f38])).
% 3.71/1.00  
% 3.71/1.00  fof(f93,plain,(
% 3.71/1.00    ~r1_tsep_1(sK10,sK8) | ~r1_tsep_1(sK8,sK10)),
% 3.71/1.00    inference(cnf_transformation,[],[f54])).
% 3.71/1.00  
% 3.71/1.00  fof(f86,plain,(
% 3.71/1.00    ( ! [X0,X1] : (r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f49])).
% 3.71/1.00  
% 3.71/1.00  cnf(c_8,plain,
% 3.71/1.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3604,plain,
% 3.71/1.00      ( r1_xboole_0(X0,X1) = iProver_top
% 3.71/1.00      | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_29,plain,
% 3.71/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_37,negated_conjecture,
% 3.71/1.00      ( m1_pre_topc(sK9,sK7) ),
% 3.71/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_631,plain,
% 3.71/1.00      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK7 != X0 | sK9 != X1 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_37]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_632,plain,
% 3.71/1.00      ( ~ l1_pre_topc(sK7) | l1_pre_topc(sK9) ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_631]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_39,negated_conjecture,
% 3.71/1.00      ( l1_pre_topc(sK7) ),
% 3.71/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_634,plain,
% 3.71/1.00      ( l1_pre_topc(sK9) ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_632,c_39]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_27,plain,
% 3.71/1.00      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_16,plain,
% 3.71/1.00      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_431,plain,
% 3.71/1.00      ( sP0(X0,X1)
% 3.71/1.00      | ~ m1_pre_topc(X0,X1)
% 3.71/1.00      | ~ l1_pre_topc(X1)
% 3.71/1.00      | ~ l1_pre_topc(X0) ),
% 3.71/1.00      inference(resolution,[status(thm)],[c_27,c_16]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_435,plain,
% 3.71/1.00      ( ~ l1_pre_topc(X1) | ~ m1_pre_topc(X0,X1) | sP0(X0,X1) ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_431,c_29]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_436,plain,
% 3.71/1.00      ( sP0(X0,X1) | ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_435]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_35,negated_conjecture,
% 3.71/1.00      ( m1_pre_topc(sK8,sK9) ),
% 3.71/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_578,plain,
% 3.71/1.00      ( sP0(X0,X1) | ~ l1_pre_topc(X1) | sK8 != X0 | sK9 != X1 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_436,c_35]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_579,plain,
% 3.71/1.00      ( sP0(sK8,sK9) | ~ l1_pre_topc(sK9) ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_578]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_641,plain,
% 3.71/1.00      ( sP0(sK8,sK9) ),
% 3.71/1.00      inference(backward_subsumption_resolution,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_634,c_579]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3581,plain,
% 3.71/1.00      ( sP0(sK8,sK9) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_641]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_26,plain,
% 3.71/1.00      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3589,plain,
% 3.71/1.00      ( sP0(X0,X1) != iProver_top
% 3.71/1.00      | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_13,plain,
% 3.71/1.00      ( ~ r1_tarski(X0,X1)
% 3.71/1.00      | ~ r1_tarski(X2,X1)
% 3.71/1.00      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3600,plain,
% 3.71/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.71/1.00      | r1_tarski(X2,X1) != iProver_top
% 3.71/1.00      | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_12,plain,
% 3.71/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3601,plain,
% 3.71/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_9,plain,
% 3.71/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.71/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3603,plain,
% 3.71/1.00      ( X0 = X1
% 3.71/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.71/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4575,plain,
% 3.71/1.00      ( k2_xboole_0(X0,X1) = X0
% 3.71/1.00      | r1_tarski(k2_xboole_0(X0,X1),X0) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_3601,c_3603]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4981,plain,
% 3.71/1.00      ( k2_xboole_0(X0,X1) = X0
% 3.71/1.00      | r1_tarski(X0,X0) != iProver_top
% 3.71/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_3600,c_4575]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_11,plain,
% 3.71/1.00      ( r1_tarski(X0,X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_106,plain,
% 3.71/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5134,plain,
% 3.71/1.00      ( k2_xboole_0(X0,X1) = X0 | r1_tarski(X1,X0) != iProver_top ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_4981,c_106]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5143,plain,
% 3.71/1.00      ( k2_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X0)
% 3.71/1.00      | sP0(X1,X0) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_3589,c_5134]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5388,plain,
% 3.71/1.00      ( k2_xboole_0(k2_struct_0(sK9),k2_struct_0(sK8)) = k2_struct_0(sK9) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_3581,c_5143]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3,plain,
% 3.71/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3609,plain,
% 3.71/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.71/1.00      | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6802,plain,
% 3.71/1.00      ( r2_hidden(X0,k2_struct_0(sK8)) != iProver_top
% 3.71/1.00      | r2_hidden(X0,k2_struct_0(sK9)) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_5388,c_3609]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_9888,plain,
% 3.71/1.00      ( r1_xboole_0(k2_struct_0(sK8),X0) = iProver_top
% 3.71/1.00      | r2_hidden(sK3(k2_struct_0(sK8),X0),k2_struct_0(sK9)) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_3604,c_6802]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_7,plain,
% 3.71/1.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3605,plain,
% 3.71/1.00      ( r1_xboole_0(X0,X1) = iProver_top
% 3.71/1.00      | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_28,plain,
% 3.71/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_687,plain,
% 3.71/1.00      ( l1_struct_0(X0) | sK9 != X0 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_634]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_688,plain,
% 3.71/1.00      ( l1_struct_0(sK9) ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_687]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3577,plain,
% 3.71/1.00      ( l1_struct_0(sK9) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_688]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_14,plain,
% 3.71/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3599,plain,
% 3.71/1.00      ( u1_struct_0(X0) = k2_struct_0(X0)
% 3.71/1.00      | l1_struct_0(X0) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4067,plain,
% 3.71/1.00      ( u1_struct_0(sK9) = k2_struct_0(sK9) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_3577,c_3599]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_36,negated_conjecture,
% 3.71/1.00      ( m1_pre_topc(sK10,sK7) ),
% 3.71/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_609,plain,
% 3.71/1.00      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK7 != X0 | sK10 != X1 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_36]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_610,plain,
% 3.71/1.00      ( ~ l1_pre_topc(sK7) | l1_pre_topc(sK10) ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_609]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_612,plain,
% 3.71/1.00      ( l1_pre_topc(sK10) ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_610,c_39]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_680,plain,
% 3.71/1.00      ( l1_struct_0(X0) | sK10 != X0 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_612]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_681,plain,
% 3.71/1.00      ( l1_struct_0(sK10) ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_680]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3578,plain,
% 3.71/1.00      ( l1_struct_0(sK10) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_681]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4065,plain,
% 3.71/1.00      ( u1_struct_0(sK10) = k2_struct_0(sK10) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_3578,c_3599]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_31,plain,
% 3.71/1.00      ( ~ r1_tsep_1(X0,X1)
% 3.71/1.00      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 3.71/1.00      | ~ l1_struct_0(X0)
% 3.71/1.00      | ~ l1_struct_0(X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3587,plain,
% 3.71/1.00      ( r1_tsep_1(X0,X1) != iProver_top
% 3.71/1.00      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.71/1.00      | l1_struct_0(X0) != iProver_top
% 3.71/1.00      | l1_struct_0(X1) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5585,plain,
% 3.71/1.00      ( r1_tsep_1(sK10,X0) != iProver_top
% 3.71/1.00      | r1_xboole_0(k2_struct_0(sK10),u1_struct_0(X0)) = iProver_top
% 3.71/1.00      | l1_struct_0(X0) != iProver_top
% 3.71/1.00      | l1_struct_0(sK10) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_4065,c_3587]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_40,plain,
% 3.71/1.00      ( l1_pre_topc(sK7) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_55,plain,
% 3.71/1.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_57,plain,
% 3.71/1.00      ( l1_pre_topc(sK10) != iProver_top
% 3.71/1.00      | l1_struct_0(sK10) = iProver_top ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_55]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_611,plain,
% 3.71/1.00      ( l1_pre_topc(sK7) != iProver_top
% 3.71/1.00      | l1_pre_topc(sK10) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_610]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_7227,plain,
% 3.71/1.00      ( l1_struct_0(X0) != iProver_top
% 3.71/1.00      | r1_xboole_0(k2_struct_0(sK10),u1_struct_0(X0)) = iProver_top
% 3.71/1.00      | r1_tsep_1(sK10,X0) != iProver_top ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_5585,c_40,c_57,c_611]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_7228,plain,
% 3.71/1.00      ( r1_tsep_1(sK10,X0) != iProver_top
% 3.71/1.00      | r1_xboole_0(k2_struct_0(sK10),u1_struct_0(X0)) = iProver_top
% 3.71/1.00      | l1_struct_0(X0) != iProver_top ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_7227]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_7236,plain,
% 3.71/1.00      ( r1_tsep_1(sK10,sK9) != iProver_top
% 3.71/1.00      | r1_xboole_0(k2_struct_0(sK10),k2_struct_0(sK9)) = iProver_top
% 3.71/1.00      | l1_struct_0(sK9) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_4067,c_7228]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_689,plain,
% 3.71/1.00      ( l1_struct_0(sK9) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_688]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_33,negated_conjecture,
% 3.71/1.00      ( r1_tsep_1(sK9,sK10) | r1_tsep_1(sK10,sK9) ),
% 3.71/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3585,plain,
% 3.71/1.00      ( r1_tsep_1(sK9,sK10) = iProver_top
% 3.71/1.00      | r1_tsep_1(sK10,sK9) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_32,plain,
% 3.71/1.00      ( ~ r1_tsep_1(X0,X1)
% 3.71/1.00      | r1_tsep_1(X1,X0)
% 3.71/1.00      | ~ l1_struct_0(X0)
% 3.71/1.00      | ~ l1_struct_0(X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3586,plain,
% 3.71/1.00      ( r1_tsep_1(X0,X1) != iProver_top
% 3.71/1.00      | r1_tsep_1(X1,X0) = iProver_top
% 3.71/1.00      | l1_struct_0(X0) != iProver_top
% 3.71/1.00      | l1_struct_0(X1) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4426,plain,
% 3.71/1.00      ( r1_tsep_1(sK10,sK9) = iProver_top
% 3.71/1.00      | l1_struct_0(sK9) != iProver_top
% 3.71/1.00      | l1_struct_0(sK10) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_3585,c_3586]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_11809,plain,
% 3.71/1.00      ( r1_xboole_0(k2_struct_0(sK10),k2_struct_0(sK9)) = iProver_top ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_7236,c_40,c_57,c_611,c_689,c_4426]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6,plain,
% 3.71/1.00      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3606,plain,
% 3.71/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 3.71/1.00      | r2_hidden(X2,X1) != iProver_top
% 3.71/1.00      | r2_hidden(X2,X0) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_11814,plain,
% 3.71/1.00      ( r2_hidden(X0,k2_struct_0(sK9)) != iProver_top
% 3.71/1.00      | r2_hidden(X0,k2_struct_0(sK10)) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_11809,c_3606]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_12044,plain,
% 3.71/1.00      ( r1_xboole_0(X0,k2_struct_0(sK10)) = iProver_top
% 3.71/1.00      | r2_hidden(sK3(X0,k2_struct_0(sK10)),k2_struct_0(sK9)) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_3605,c_11814]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_16159,plain,
% 3.71/1.00      ( r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK10)) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_9888,c_12044]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_588,plain,
% 3.71/1.00      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK8 != X1 | sK9 != X0 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_35]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_589,plain,
% 3.71/1.00      ( l1_pre_topc(sK8) | ~ l1_pre_topc(sK9) ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_588]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_642,plain,
% 3.71/1.00      ( l1_pre_topc(sK8) ),
% 3.71/1.00      inference(backward_subsumption_resolution,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_634,c_589]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_694,plain,
% 3.71/1.00      ( l1_struct_0(X0) | sK8 != X0 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_642]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_695,plain,
% 3.71/1.00      ( l1_struct_0(sK8) ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_694]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3576,plain,
% 3.71/1.00      ( l1_struct_0(sK8) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_695]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4068,plain,
% 3.71/1.00      ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_3576,c_3599]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5586,plain,
% 3.71/1.00      ( r1_tsep_1(sK8,X0) != iProver_top
% 3.71/1.00      | r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X0)) = iProver_top
% 3.71/1.00      | l1_struct_0(X0) != iProver_top
% 3.71/1.00      | l1_struct_0(sK8) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_4068,c_3587]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_696,plain,
% 3.71/1.00      ( l1_struct_0(sK8) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_695]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_8563,plain,
% 3.71/1.00      ( l1_struct_0(X0) != iProver_top
% 3.71/1.00      | r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X0)) = iProver_top
% 3.71/1.00      | r1_tsep_1(sK8,X0) != iProver_top ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_5586,c_696]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_8564,plain,
% 3.71/1.00      ( r1_tsep_1(sK8,X0) != iProver_top
% 3.71/1.00      | r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X0)) = iProver_top
% 3.71/1.00      | l1_struct_0(X0) != iProver_top ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_8563]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_8572,plain,
% 3.71/1.00      ( r1_tsep_1(sK8,sK10) != iProver_top
% 3.71/1.00      | r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK10)) = iProver_top
% 3.71/1.00      | l1_struct_0(sK10) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_4065,c_8564]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_34,negated_conjecture,
% 3.71/1.00      ( ~ r1_tsep_1(sK8,sK10) | ~ r1_tsep_1(sK10,sK8) ),
% 3.71/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_45,plain,
% 3.71/1.00      ( r1_tsep_1(sK8,sK10) != iProver_top
% 3.71/1.00      | r1_tsep_1(sK10,sK8) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4042,plain,
% 3.71/1.00      ( ~ r1_tsep_1(sK8,sK10)
% 3.71/1.00      | r1_tsep_1(sK10,sK8)
% 3.71/1.00      | ~ l1_struct_0(sK8)
% 3.71/1.00      | ~ l1_struct_0(sK10) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_32]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4043,plain,
% 3.71/1.00      ( r1_tsep_1(sK8,sK10) != iProver_top
% 3.71/1.00      | r1_tsep_1(sK10,sK8) = iProver_top
% 3.71/1.00      | l1_struct_0(sK8) != iProver_top
% 3.71/1.00      | l1_struct_0(sK10) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_4042]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_13482,plain,
% 3.71/1.00      ( r1_tsep_1(sK8,sK10) != iProver_top ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_8572,c_40,c_45,c_57,c_611,c_696,c_4043]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2932,plain,
% 3.71/1.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.71/1.00      theory(equality) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4030,plain,
% 3.71/1.00      ( ~ r1_xboole_0(X0,X1)
% 3.71/1.00      | r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10))
% 3.71/1.00      | u1_struct_0(sK8) != X0
% 3.71/1.00      | u1_struct_0(sK10) != X1 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_2932]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4189,plain,
% 3.71/1.00      ( r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10))
% 3.71/1.00      | ~ r1_xboole_0(k2_struct_0(sK8),X0)
% 3.71/1.00      | u1_struct_0(sK8) != k2_struct_0(sK8)
% 3.71/1.00      | u1_struct_0(sK10) != X0 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_4030]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4508,plain,
% 3.71/1.00      ( r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10))
% 3.71/1.00      | ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK10))
% 3.71/1.00      | u1_struct_0(sK8) != k2_struct_0(sK8)
% 3.71/1.00      | u1_struct_0(sK10) != k2_struct_0(sK10) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_4189]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4510,plain,
% 3.71/1.00      ( u1_struct_0(sK8) != k2_struct_0(sK8)
% 3.71/1.00      | u1_struct_0(sK10) != k2_struct_0(sK10)
% 3.71/1.00      | r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10)) = iProver_top
% 3.71/1.00      | r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK10)) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_4508]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_30,plain,
% 3.71/1.00      ( r1_tsep_1(X0,X1)
% 3.71/1.00      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 3.71/1.00      | ~ l1_struct_0(X0)
% 3.71/1.00      | ~ l1_struct_0(X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3896,plain,
% 3.71/1.00      ( r1_tsep_1(sK8,sK10)
% 3.71/1.00      | ~ r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10))
% 3.71/1.00      | ~ l1_struct_0(sK8)
% 3.71/1.00      | ~ l1_struct_0(sK10) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_30]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3897,plain,
% 3.71/1.00      ( r1_tsep_1(sK8,sK10) = iProver_top
% 3.71/1.00      | r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK10)) != iProver_top
% 3.71/1.00      | l1_struct_0(sK8) != iProver_top
% 3.71/1.00      | l1_struct_0(sK10) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_3896]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_98,plain,
% 3.71/1.00      ( ~ l1_struct_0(sK10) | u1_struct_0(sK10) = k2_struct_0(sK10) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_56,plain,
% 3.71/1.00      ( ~ l1_pre_topc(sK10) | l1_struct_0(sK10) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_28]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(contradiction,plain,
% 3.71/1.00      ( $false ),
% 3.71/1.00      inference(minisat,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_16159,c_13482,c_4510,c_4068,c_3897,c_696,c_611,c_610,
% 3.71/1.00                 c_98,c_57,c_56,c_40,c_39]) ).
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  ------                               Statistics
% 3.71/1.00  
% 3.71/1.00  ------ General
% 3.71/1.00  
% 3.71/1.00  abstr_ref_over_cycles:                  0
% 3.71/1.00  abstr_ref_under_cycles:                 0
% 3.71/1.00  gc_basic_clause_elim:                   0
% 3.71/1.00  forced_gc_time:                         0
% 3.71/1.00  parsing_time:                           0.01
% 3.71/1.00  unif_index_cands_time:                  0.
% 3.71/1.00  unif_index_add_time:                    0.
% 3.71/1.00  orderings_time:                         0.
% 3.71/1.00  out_proof_time:                         0.013
% 3.71/1.00  total_time:                             0.406
% 3.71/1.00  num_of_symbols:                         56
% 3.71/1.00  num_of_terms:                           14211
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing
% 3.71/1.00  
% 3.71/1.00  num_of_splits:                          0
% 3.71/1.00  num_of_split_atoms:                     0
% 3.71/1.00  num_of_reused_defs:                     0
% 3.71/1.00  num_eq_ax_congr_red:                    56
% 3.71/1.00  num_of_sem_filtered_clauses:            1
% 3.71/1.00  num_of_subtypes:                        0
% 3.71/1.00  monotx_restored_types:                  0
% 3.71/1.00  sat_num_of_epr_types:                   0
% 3.71/1.00  sat_num_of_non_cyclic_types:            0
% 3.71/1.00  sat_guarded_non_collapsed_types:        0
% 3.71/1.00  num_pure_diseq_elim:                    0
% 3.71/1.00  simp_replaced_by:                       0
% 3.71/1.00  res_preprocessed:                       173
% 3.71/1.00  prep_upred:                             0
% 3.71/1.00  prep_unflattend:                        192
% 3.71/1.00  smt_new_axioms:                         0
% 3.71/1.00  pred_elim_cands:                        7
% 3.71/1.00  pred_elim:                              3
% 3.71/1.00  pred_elim_cl:                           2
% 3.71/1.00  pred_elim_cycles:                       7
% 3.71/1.00  merged_defs:                            0
% 3.71/1.00  merged_defs_ncl:                        0
% 3.71/1.00  bin_hyper_res:                          0
% 3.71/1.00  prep_cycles:                            4
% 3.71/1.00  pred_elim_time:                         0.042
% 3.71/1.00  splitting_time:                         0.
% 3.71/1.00  sem_filter_time:                        0.
% 3.71/1.00  monotx_time:                            0.
% 3.71/1.00  subtype_inf_time:                       0.
% 3.71/1.00  
% 3.71/1.00  ------ Problem properties
% 3.71/1.00  
% 3.71/1.00  clauses:                                37
% 3.71/1.00  conjectures:                            2
% 3.71/1.00  epr:                                    14
% 3.71/1.00  horn:                                   28
% 3.71/1.00  ground:                                 10
% 3.71/1.00  unary:                                  10
% 3.71/1.00  binary:                                 8
% 3.71/1.00  lits:                                   98
% 3.71/1.00  lits_eq:                                8
% 3.71/1.00  fd_pure:                                0
% 3.71/1.00  fd_pseudo:                              0
% 3.71/1.00  fd_cond:                                0
% 3.71/1.00  fd_pseudo_cond:                         4
% 3.71/1.00  ac_symbols:                             0
% 3.71/1.00  
% 3.71/1.00  ------ Propositional Solver
% 3.71/1.00  
% 3.71/1.00  prop_solver_calls:                      30
% 3.71/1.00  prop_fast_solver_calls:                 1881
% 3.71/1.00  smt_solver_calls:                       0
% 3.71/1.00  smt_fast_solver_calls:                  0
% 3.71/1.00  prop_num_of_clauses:                    6537
% 3.71/1.00  prop_preprocess_simplified:             14459
% 3.71/1.00  prop_fo_subsumed:                       60
% 3.71/1.00  prop_solver_time:                       0.
% 3.71/1.00  smt_solver_time:                        0.
% 3.71/1.00  smt_fast_solver_time:                   0.
% 3.71/1.00  prop_fast_solver_time:                  0.
% 3.71/1.00  prop_unsat_core_time:                   0.001
% 3.71/1.00  
% 3.71/1.00  ------ QBF
% 3.71/1.00  
% 3.71/1.00  qbf_q_res:                              0
% 3.71/1.00  qbf_num_tautologies:                    0
% 3.71/1.00  qbf_prep_cycles:                        0
% 3.71/1.00  
% 3.71/1.00  ------ BMC1
% 3.71/1.00  
% 3.71/1.00  bmc1_current_bound:                     -1
% 3.71/1.00  bmc1_last_solved_bound:                 -1
% 3.71/1.00  bmc1_unsat_core_size:                   -1
% 3.71/1.00  bmc1_unsat_core_parents_size:           -1
% 3.71/1.00  bmc1_merge_next_fun:                    0
% 3.71/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.71/1.00  
% 3.71/1.00  ------ Instantiation
% 3.71/1.00  
% 3.71/1.00  inst_num_of_clauses:                    1549
% 3.71/1.00  inst_num_in_passive:                    210
% 3.71/1.00  inst_num_in_active:                     624
% 3.71/1.00  inst_num_in_unprocessed:                715
% 3.71/1.00  inst_num_of_loops:                      690
% 3.71/1.00  inst_num_of_learning_restarts:          0
% 3.71/1.00  inst_num_moves_active_passive:          63
% 3.71/1.00  inst_lit_activity:                      0
% 3.71/1.00  inst_lit_activity_moves:                1
% 3.71/1.00  inst_num_tautologies:                   0
% 3.71/1.00  inst_num_prop_implied:                  0
% 3.71/1.00  inst_num_existing_simplified:           0
% 3.71/1.00  inst_num_eq_res_simplified:             0
% 3.71/1.00  inst_num_child_elim:                    0
% 3.71/1.00  inst_num_of_dismatching_blockings:      468
% 3.71/1.00  inst_num_of_non_proper_insts:           1614
% 3.71/1.00  inst_num_of_duplicates:                 0
% 3.71/1.00  inst_inst_num_from_inst_to_res:         0
% 3.71/1.00  inst_dismatching_checking_time:         0.
% 3.71/1.00  
% 3.71/1.00  ------ Resolution
% 3.71/1.00  
% 3.71/1.00  res_num_of_clauses:                     0
% 3.71/1.00  res_num_in_passive:                     0
% 3.71/1.00  res_num_in_active:                      0
% 3.71/1.00  res_num_of_loops:                       177
% 3.71/1.00  res_forward_subset_subsumed:            35
% 3.71/1.00  res_backward_subset_subsumed:           0
% 3.71/1.00  res_forward_subsumed:                   0
% 3.71/1.00  res_backward_subsumed:                  0
% 3.71/1.00  res_forward_subsumption_resolution:     0
% 3.71/1.00  res_backward_subsumption_resolution:    2
% 3.71/1.00  res_clause_to_clause_subsumption:       864
% 3.71/1.00  res_orphan_elimination:                 0
% 3.71/1.00  res_tautology_del:                      56
% 3.71/1.00  res_num_eq_res_simplified:              0
% 3.71/1.00  res_num_sel_changes:                    0
% 3.71/1.00  res_moves_from_active_to_pass:          0
% 3.71/1.00  
% 3.71/1.00  ------ Superposition
% 3.71/1.00  
% 3.71/1.00  sup_time_total:                         0.
% 3.71/1.00  sup_time_generating:                    0.
% 3.71/1.00  sup_time_sim_full:                      0.
% 3.71/1.00  sup_time_sim_immed:                     0.
% 3.71/1.00  
% 3.71/1.00  sup_num_of_clauses:                     261
% 3.71/1.00  sup_num_in_active:                      131
% 3.71/1.00  sup_num_in_passive:                     130
% 3.71/1.00  sup_num_of_loops:                       136
% 3.71/1.00  sup_fw_superposition:                   233
% 3.71/1.00  sup_bw_superposition:                   121
% 3.71/1.00  sup_immediate_simplified:               58
% 3.71/1.00  sup_given_eliminated:                   0
% 3.71/1.00  comparisons_done:                       0
% 3.71/1.00  comparisons_avoided:                    0
% 3.71/1.00  
% 3.71/1.00  ------ Simplifications
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  sim_fw_subset_subsumed:                 31
% 3.71/1.00  sim_bw_subset_subsumed:                 11
% 3.71/1.00  sim_fw_subsumed:                        15
% 3.71/1.00  sim_bw_subsumed:                        0
% 3.71/1.00  sim_fw_subsumption_res:                 0
% 3.71/1.00  sim_bw_subsumption_res:                 0
% 3.71/1.00  sim_tautology_del:                      41
% 3.71/1.00  sim_eq_tautology_del:                   1
% 3.71/1.00  sim_eq_res_simp:                        6
% 3.71/1.00  sim_fw_demodulated:                     2
% 3.71/1.00  sim_bw_demodulated:                     0
% 3.71/1.00  sim_light_normalised:                   13
% 3.71/1.00  sim_joinable_taut:                      0
% 3.71/1.00  sim_joinable_simp:                      0
% 3.71/1.00  sim_ac_normalised:                      0
% 3.71/1.00  sim_smt_subsumption:                    0
% 3.71/1.00  
%------------------------------------------------------------------------------
