%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:52 EST 2020

% Result     : Theorem 19.41s
% Output     : CNFRefutation 19.41s
% Verified   : 
% Statistics : Number of formulae       :  247 (2310 expanded)
%              Number of clauses        :  168 ( 675 expanded)
%              Number of leaves         :   29 ( 629 expanded)
%              Depth                    :   26
%              Number of atoms          :  755 (13964 expanded)
%              Number of equality atoms :  287 ( 710 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f93,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f55,f60,f60])).

fof(f17,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
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
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f20,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
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
    inference(pure_predicate_removal,[],[f18])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( r1_tsep_1(X2,X1)
            | r1_tsep_1(X1,X2) )
          & m1_pre_topc(X1,X2)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ( r1_tsep_1(sK8,X1)
          | r1_tsep_1(X1,sK8) )
        & m1_pre_topc(X1,sK8)
        & m1_pre_topc(sK8,X0)
        & ~ v2_struct_0(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( r1_tsep_1(X2,sK7)
              | r1_tsep_1(sK7,X2) )
            & m1_pre_topc(sK7,X2)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK7,X0)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( r1_tsep_1(X2,X1)
                  | r1_tsep_1(X1,X2) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,sK6)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK6)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( r1_tsep_1(sK8,sK7)
      | r1_tsep_1(sK7,sK8) )
    & m1_pre_topc(sK7,sK8)
    & m1_pre_topc(sK8,sK6)
    & ~ v2_struct_0(sK8)
    & m1_pre_topc(sK7,sK6)
    & ~ v2_struct_0(sK7)
    & l1_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f35,f53,f52,f51])).

fof(f91,plain,(
    m1_pre_topc(sK7,sK8) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f36,plain,(
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

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f26,f37,f36])).

fof(f78,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f66,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f80,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f90,plain,(
    m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f54])).

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
    inference(nnf_transformation,[],[f36])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f48,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK4(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
              ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK3(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK3(X0,X1),u1_pre_topc(X0)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK3(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X1))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK3(X0,X1),u1_pre_topc(X0)) )
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK3(X0,X1)
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK3(X0,X1),u1_pre_topc(X0)) )
          & ( ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1),k2_struct_0(X0)) = sK3(X0,X1)
              & r2_hidden(sK4(X0,X1),u1_pre_topc(X1))
              & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK3(X0,X1),u1_pre_topc(X0)) )
          & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ( k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X5),k2_struct_0(X0)) = X5
                    & r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X1))
                    & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f45,f48,f47,f46])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f60])).

fof(f92,plain,
    ( r1_tsep_1(sK8,sK7)
    | r1_tsep_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f79,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f21,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f39])).

fof(f56,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f87,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_47684,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_47687,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_48683,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_47684,c_47687])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_47683,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_48783,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_48683,c_47683])).

cnf(c_48488,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_47684,c_47683])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_48490,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_48488,c_0])).

cnf(c_49913,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_48783,c_48490])).

cnf(c_49914,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_49913,c_48783])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK7,sK8) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_47672,plain,
    ( m1_pre_topc(sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_22,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_47678,plain,
    ( sP1(X0,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_11,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_47680,plain,
    ( sP1(X0,X1) != iProver_top
    | sP0(X1,X0) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_49910,plain,
    ( sP0(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_47678,c_47680])).

cnf(c_3974,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_11,c_22])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4015,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X0,X1)
    | sP0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3974,c_24])).

cnf(c_4016,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_4015])).

cnf(c_4017,plain,
    ( sP0(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4016])).

cnf(c_55718,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | sP0(X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49910,c_4017])).

cnf(c_55719,plain,
    ( sP0(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_55718])).

cnf(c_55725,plain,
    ( sP0(sK7,sK8) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_47672,c_55719])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_38,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_43,plain,
    ( m1_pre_topc(sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3652,plain,
    ( ~ sP1(sK8,sK7)
    | sP0(sK7,sK8)
    | ~ m1_pre_topc(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3653,plain,
    ( sP1(sK8,sK7) != iProver_top
    | sP0(sK7,sK8) = iProver_top
    | m1_pre_topc(sK7,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3652])).

cnf(c_3665,plain,
    ( sP1(sK8,sK7)
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3666,plain,
    ( sP1(sK8,sK7) = iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3665])).

cnf(c_3713,plain,
    ( l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK8) ),
    inference(resolution,[status(thm)],[c_24,c_30])).

cnf(c_3714,plain,
    ( l1_pre_topc(sK7) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3713])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3715,plain,
    ( ~ l1_pre_topc(sK6)
    | l1_pre_topc(sK8) ),
    inference(resolution,[status(thm)],[c_24,c_31])).

cnf(c_3716,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3715])).

cnf(c_55969,plain,
    ( sP0(sK7,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_55725,c_38,c_43,c_3653,c_3666,c_3714,c_3716])).

cnf(c_21,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_47679,plain,
    ( sP0(X0,X1) != iProver_top
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_47686,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_49021,plain,
    ( k4_xboole_0(k2_struct_0(X0),k4_xboole_0(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0)
    | sP0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_47679,c_47686])).

cnf(c_56344,plain,
    ( k4_xboole_0(k2_struct_0(sK7),k4_xboole_0(k2_struct_0(sK7),k2_struct_0(sK8))) = k2_struct_0(sK7) ),
    inference(superposition,[status(thm)],[c_55969,c_49021])).

cnf(c_29,negated_conjecture,
    ( r1_tsep_1(sK7,sK8)
    | r1_tsep_1(sK8,sK7) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_23,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_57,plain,
    ( ~ l1_pre_topc(sK7)
    | l1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_3756,plain,
    ( l1_pre_topc(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3715,c_35])).

cnf(c_3816,plain,
    ( l1_struct_0(sK8) ),
    inference(resolution,[status(thm)],[c_3756,c_23])).

cnf(c_28,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_23215,plain,
    ( r1_tsep_1(sK7,sK8)
    | ~ r1_tsep_1(sK8,sK7)
    | ~ l1_struct_0(sK7)
    | ~ l1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_23248,plain,
    ( ~ r1_tsep_1(sK7,sK8)
    | r1_tsep_1(sK8,sK7)
    | ~ l1_struct_0(sK7)
    | ~ l1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_47559,negated_conjecture,
    ( r1_tsep_1(sK8,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29,c_35,c_57,c_3713,c_3715,c_3816,c_23215,c_23248])).

cnf(c_47665,plain,
    ( r1_tsep_1(sK8,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47559])).

cnf(c_47673,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_tsep_1(X1,X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_48094,plain,
    ( r1_tsep_1(sK7,sK8) = iProver_top
    | l1_struct_0(sK7) != iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_47665,c_47673])).

cnf(c_23227,negated_conjecture,
    ( r1_tsep_1(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29,c_35,c_57,c_3713,c_3715,c_3816,c_23215])).

cnf(c_23229,plain,
    ( r1_tsep_1(sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23227])).

cnf(c_48383,plain,
    ( r1_tsep_1(sK7,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_48094,c_23229])).

cnf(c_27,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_47674,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_48794,plain,
    ( k4_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(X0)
    | r1_tsep_1(X0,X1) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_47674,c_47683])).

cnf(c_51952,plain,
    ( k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) = u1_struct_0(sK7)
    | l1_struct_0(sK7) != iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_48383,c_48794])).

cnf(c_47676,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_49772,plain,
    ( l1_pre_topc(sK7) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_47672,c_47676])).

cnf(c_50160,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49772,c_38,c_3714,c_3716])).

cnf(c_47677,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_50165,plain,
    ( l1_struct_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_50160,c_47677])).

cnf(c_9,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_47681,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_50277,plain,
    ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
    inference(superposition,[status(thm)],[c_50165,c_47681])).

cnf(c_47671,plain,
    ( m1_pre_topc(sK8,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_49773,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_47671,c_47676])).

cnf(c_50263,plain,
    ( l1_pre_topc(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49773,c_38,c_3716])).

cnf(c_50268,plain,
    ( l1_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_50263,c_47677])).

cnf(c_50412,plain,
    ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(superposition,[status(thm)],[c_50268,c_47681])).

cnf(c_51964,plain,
    ( k4_xboole_0(k2_struct_0(sK7),k2_struct_0(sK8)) = k2_struct_0(sK7)
    | l1_struct_0(sK7) != iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_51952,c_50277,c_50412])).

cnf(c_99,plain,
    ( ~ l1_struct_0(sK7)
    | u1_struct_0(sK7) = k2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_402,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_6797,plain,
    ( X0 != X1
    | X0 = u1_struct_0(X2)
    | u1_struct_0(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_402])).

cnf(c_7010,plain,
    ( X0 = u1_struct_0(X1)
    | X0 != k2_struct_0(X1)
    | u1_struct_0(X1) != k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_6797])).

cnf(c_7017,plain,
    ( u1_struct_0(X0) != k2_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0)
    | k2_struct_0(X0) != k2_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_7010])).

cnf(c_7018,plain,
    ( u1_struct_0(X0) != k2_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(equality_resolution_simp,[status(thm)],[c_7017])).

cnf(c_7019,plain,
    ( u1_struct_0(sK7) != k2_struct_0(sK7)
    | k2_struct_0(sK7) = u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_7018])).

cnf(c_5663,negated_conjecture,
    ( arAF0_m1_pre_topc_0_1(sK8)
    | ~ iProver_ARSWP_115 ),
    inference(arg_filter_abstr,[status(unp)],[c_31])).

cnf(c_6280,plain,
    ( arAF0_m1_pre_topc_0_1(sK8) = iProver_top
    | iProver_ARSWP_115 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5663])).

cnf(c_5657,plain,
    ( ~ arAF0_m1_pre_topc_0_1(X0)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0)
    | ~ iProver_ARSWP_109 ),
    inference(arg_filter_abstr,[status(unp)],[c_24])).

cnf(c_6285,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_109 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5657])).

cnf(c_6770,plain,
    ( ~ arAF0_m1_pre_topc_0_1(X0)
    | l1_pre_topc(X0)
    | ~ iProver_ARSWP_109 ),
    inference(resolution,[status(thm)],[c_5657,c_35])).

cnf(c_6771,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_109 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6770])).

cnf(c_6820,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_109 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6285,c_6771])).

cnf(c_6828,plain,
    ( l1_pre_topc(sK8) = iProver_top
    | iProver_ARSWP_115 != iProver_top
    | iProver_ARSWP_109 != iProver_top ),
    inference(superposition,[status(thm)],[c_6280,c_6820])).

cnf(c_7227,plain,
    ( l1_pre_topc(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6828,c_38,c_3716])).

cnf(c_6314,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7232,plain,
    ( l1_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_7227,c_6314])).

cnf(c_6315,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7377,plain,
    ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(superposition,[status(thm)],[c_7232,c_6315])).

cnf(c_10772,plain,
    ( ~ r1_tsep_1(sK7,sK8)
    | r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))
    | ~ l1_struct_0(sK7)
    | ~ l1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_25440,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK8)
    | u1_struct_0(sK8) != X1 ),
    inference(instantiation,[status(thm)],[c_402])).

cnf(c_25570,plain,
    ( X0 = u1_struct_0(sK8)
    | X0 != k2_struct_0(sK8)
    | u1_struct_0(sK8) != k2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_25440])).

cnf(c_25627,plain,
    ( u1_struct_0(sK8) != k2_struct_0(sK8)
    | k2_struct_0(sK8) = u1_struct_0(sK8)
    | k2_struct_0(sK8) != k2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_25570])).

cnf(c_25628,plain,
    ( u1_struct_0(sK8) != k2_struct_0(sK8)
    | k2_struct_0(sK8) = u1_struct_0(sK8) ),
    inference(equality_resolution_simp,[status(thm)],[c_25627])).

cnf(c_406,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_25383,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))
    | X0 != u1_struct_0(sK7)
    | X1 != u1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_406])).

cnf(c_25557,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))
    | r1_xboole_0(k2_struct_0(sK7),X0)
    | X0 != u1_struct_0(sK8)
    | k2_struct_0(sK7) != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_25383])).

cnf(c_26728,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))
    | r1_xboole_0(k2_struct_0(sK7),k2_struct_0(sK8))
    | k2_struct_0(sK7) != u1_struct_0(sK7)
    | k2_struct_0(sK8) != u1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_25557])).

cnf(c_31434,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK7),k2_struct_0(sK8))
    | k4_xboole_0(k2_struct_0(sK7),k2_struct_0(sK8)) = k2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_52599,plain,
    ( k4_xboole_0(k2_struct_0(sK7),k2_struct_0(sK8)) = k2_struct_0(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_51964,c_35,c_29,c_57,c_99,c_3713,c_3715,c_3816,c_7019,c_7377,c_10772,c_23215,c_25628,c_26728,c_31434])).

cnf(c_52602,plain,
    ( k4_xboole_0(k2_struct_0(sK8),k4_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))) = k4_xboole_0(k2_struct_0(sK7),k2_struct_0(sK7)) ),
    inference(superposition,[status(thm)],[c_52599,c_0])).

cnf(c_51953,plain,
    ( k4_xboole_0(u1_struct_0(sK8),u1_struct_0(sK7)) = u1_struct_0(sK8)
    | l1_struct_0(sK7) != iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_47665,c_48794])).

cnf(c_51957,plain,
    ( k4_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) = k2_struct_0(sK8)
    | l1_struct_0(sK7) != iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_51953,c_50277,c_50412])).

cnf(c_23844,negated_conjecture,
    ( arAF0_m1_pre_topc_0_1(sK8)
    | ~ iProver_ARSWP_171 ),
    inference(arg_filter_abstr,[status(unp)],[c_31])).

cnf(c_24650,plain,
    ( arAF0_m1_pre_topc_0_1(sK8) = iProver_top
    | iProver_ARSWP_171 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23844])).

cnf(c_23842,plain,
    ( ~ arAF0_m1_pre_topc_0_1(X0)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0)
    | ~ iProver_ARSWP_169 ),
    inference(arg_filter_abstr,[status(unp)],[c_24])).

cnf(c_24652,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_169 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23842])).

cnf(c_25191,plain,
    ( ~ arAF0_m1_pre_topc_0_1(X0)
    | l1_pre_topc(X0)
    | ~ iProver_ARSWP_169 ),
    inference(resolution,[status(thm)],[c_23842,c_35])).

cnf(c_25192,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_169 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25191])).

cnf(c_25248,plain,
    ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | iProver_ARSWP_169 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24652,c_25192])).

cnf(c_25256,plain,
    ( l1_pre_topc(sK8) = iProver_top
    | iProver_ARSWP_171 != iProver_top
    | iProver_ARSWP_169 != iProver_top ),
    inference(superposition,[status(thm)],[c_24650,c_25248])).

cnf(c_25600,plain,
    ( l1_pre_topc(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25256,c_38,c_3716])).

cnf(c_24681,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_25605,plain,
    ( l1_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_25600,c_24681])).

cnf(c_24682,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_25724,plain,
    ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(superposition,[status(thm)],[c_25605,c_24682])).

cnf(c_23843,negated_conjecture,
    ( arAF0_m1_pre_topc_0_1(sK7)
    | ~ iProver_ARSWP_170 ),
    inference(arg_filter_abstr,[status(unp)],[c_30])).

cnf(c_24651,plain,
    ( arAF0_m1_pre_topc_0_1(sK7) = iProver_top
    | iProver_ARSWP_170 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23843])).

cnf(c_25255,plain,
    ( l1_pre_topc(sK7) = iProver_top
    | iProver_ARSWP_170 != iProver_top
    | iProver_ARSWP_169 != iProver_top ),
    inference(superposition,[status(thm)],[c_24651,c_25248])).

cnf(c_25592,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25255,c_38,c_3714,c_3716])).

cnf(c_25597,plain,
    ( l1_struct_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_25592,c_24681])).

cnf(c_25721,plain,
    ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
    inference(superposition,[status(thm)],[c_25597,c_24682])).

cnf(c_24678,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_27931,plain,
    ( r1_tsep_1(sK7,X0) != iProver_top
    | r1_xboole_0(k2_struct_0(sK7),u1_struct_0(X0)) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_25721,c_24678])).

cnf(c_56,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_58,plain,
    ( l1_pre_topc(sK7) != iProver_top
    | l1_struct_0(sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_29308,plain,
    ( l1_struct_0(X0) != iProver_top
    | r1_xboole_0(k2_struct_0(sK7),u1_struct_0(X0)) = iProver_top
    | r1_tsep_1(sK7,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27931,c_38,c_58,c_3714,c_3716])).

cnf(c_29309,plain,
    ( r1_tsep_1(sK7,X0) != iProver_top
    | r1_xboole_0(k2_struct_0(sK7),u1_struct_0(X0)) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_29308])).

cnf(c_29317,plain,
    ( r1_tsep_1(sK7,sK8) != iProver_top
    | r1_xboole_0(k2_struct_0(sK7),k2_struct_0(sK8)) = iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_25724,c_29309])).

cnf(c_3817,plain,
    ( l1_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3816])).

cnf(c_10773,plain,
    ( r1_tsep_1(sK7,sK8) != iProver_top
    | r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) = iProver_top
    | l1_struct_0(sK7) != iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10772])).

cnf(c_26729,plain,
    ( k2_struct_0(sK7) != u1_struct_0(sK7)
    | k2_struct_0(sK8) != u1_struct_0(sK8)
    | r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) != iProver_top
    | r1_xboole_0(k2_struct_0(sK7),k2_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26728])).

cnf(c_32980,plain,
    ( r1_xboole_0(k2_struct_0(sK7),k2_struct_0(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29317,c_35,c_38,c_57,c_58,c_99,c_3713,c_3714,c_3715,c_3716,c_3817,c_7019,c_7377,c_10773,c_23229,c_25628,c_26729])).

cnf(c_24689,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_32985,plain,
    ( r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_32980,c_24689])).

cnf(c_24684,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_35025,plain,
    ( k4_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) = k2_struct_0(sK8) ),
    inference(superposition,[status(thm)],[c_32985,c_24684])).

cnf(c_52335,plain,
    ( k4_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) = k2_struct_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_51957,c_35025])).

cnf(c_52604,plain,
    ( k4_xboole_0(k2_struct_0(sK8),k2_struct_0(sK8)) = k4_xboole_0(k2_struct_0(sK7),k2_struct_0(sK7)) ),
    inference(light_normalisation,[status(thm)],[c_52602,c_52335])).

cnf(c_56352,plain,
    ( k4_xboole_0(k2_struct_0(sK8),k2_struct_0(sK8)) = k2_struct_0(sK7) ),
    inference(light_normalisation,[status(thm)],[c_56344,c_52599,c_52604])).

cnf(c_57276,plain,
    ( k2_struct_0(sK7) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_49914,c_56352])).

cnf(c_404,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_6777,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_struct_0(X1))
    | k2_struct_0(X1) != X0 ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_8593,plain,
    ( v1_xboole_0(k2_struct_0(X0))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_struct_0(X0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6777])).

cnf(c_8595,plain,
    ( v1_xboole_0(k2_struct_0(sK7))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_struct_0(sK7) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8593])).

cnf(c_6654,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(X1))
    | u1_struct_0(X1) != X0 ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_6726,plain,
    ( v1_xboole_0(u1_struct_0(X0))
    | ~ v1_xboole_0(k2_struct_0(X0))
    | u1_struct_0(X0) != k2_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_6654])).

cnf(c_6728,plain,
    ( v1_xboole_0(u1_struct_0(sK7))
    | ~ v1_xboole_0(k2_struct_0(sK7))
    | u1_struct_0(sK7) != k2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_6726])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2875,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_4])).

cnf(c_1,plain,
    ( r2_hidden(sK2(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3085,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2875,c_1])).

cnf(c_25,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_53,plain,
    ( v2_struct_0(sK7)
    | ~ l1_struct_0(sK7)
    | ~ v1_xboole_0(u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f87])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_57276,c_8595,c_6728,c_3715,c_3713,c_3085,c_99,c_57,c_53,c_34,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:20:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.41/2.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.41/2.99  
% 19.41/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.41/2.99  
% 19.41/2.99  ------  iProver source info
% 19.41/2.99  
% 19.41/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.41/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.41/2.99  git: non_committed_changes: false
% 19.41/2.99  git: last_make_outside_of_git: false
% 19.41/2.99  
% 19.41/2.99  ------ 
% 19.41/2.99  ------ Parsing...
% 19.41/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.41/2.99  
% 19.41/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.41/2.99  
% 19.41/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.41/2.99  
% 19.41/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.41/2.99  ------ Proving...
% 19.41/2.99  ------ Problem Properties 
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  clauses                                 37
% 19.41/2.99  conjectures                             8
% 19.41/2.99  EPR                                     18
% 19.41/2.99  Horn                                    31
% 19.41/2.99  unary                                   10
% 19.41/2.99  binary                                  10
% 19.41/2.99  lits                                    95
% 19.41/2.99  lits eq                                 8
% 19.41/2.99  fd_pure                                 0
% 19.41/2.99  fd_pseudo                               0
% 19.41/2.99  fd_cond                                 0
% 19.41/2.99  fd_pseudo_cond                          0
% 19.41/2.99  AC symbols                              0
% 19.41/2.99  
% 19.41/2.99  ------ Input Options Time Limit: Unbounded
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  ------ Preprocessing...
% 19.41/2.99  
% 19.41/2.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 19.41/2.99  Current options:
% 19.41/2.99  ------ 
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  ------ Proving...
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.41/2.99  
% 19.41/2.99  ------ Proving...
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.41/2.99  
% 19.41/2.99  ------ Proving...
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.41/2.99  
% 19.41/2.99  ------ Proving...
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.41/2.99  
% 19.41/2.99  ------ Proving...
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.41/2.99  
% 19.41/2.99  ------ Proving...
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.41/2.99  
% 19.41/2.99  ------ Proving...
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.41/2.99  
% 19.41/2.99  ------ Proving...
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.41/2.99  
% 19.41/2.99  ------ Proving...
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.41/2.99  
% 19.41/2.99  ------ Proving...
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.41/2.99  
% 19.41/2.99  ------ Proving...
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.41/2.99  
% 19.41/2.99  ------ Proving...
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.41/2.99  
% 19.41/2.99  ------ Proving...
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.41/2.99  
% 19.41/2.99  ------ Proving...
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  % SZS status Theorem for theBenchmark.p
% 19.41/2.99  
% 19.41/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.41/2.99  
% 19.41/2.99  fof(f7,axiom,(
% 19.41/2.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 19.41/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.41/2.99  
% 19.41/2.99  fof(f61,plain,(
% 19.41/2.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 19.41/2.99    inference(cnf_transformation,[],[f7])).
% 19.41/2.99  
% 19.41/2.99  fof(f3,axiom,(
% 19.41/2.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 19.41/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.41/2.99  
% 19.41/2.99  fof(f22,plain,(
% 19.41/2.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 19.41/2.99    inference(ennf_transformation,[],[f3])).
% 19.41/2.99  
% 19.41/2.99  fof(f57,plain,(
% 19.41/2.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 19.41/2.99    inference(cnf_transformation,[],[f22])).
% 19.41/2.99  
% 19.41/2.99  fof(f8,axiom,(
% 19.41/3.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 19.41/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.41/3.00  
% 19.41/3.00  fof(f41,plain,(
% 19.41/3.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 19.41/3.00    inference(nnf_transformation,[],[f8])).
% 19.41/3.00  
% 19.41/3.00  fof(f62,plain,(
% 19.41/3.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 19.41/3.00    inference(cnf_transformation,[],[f41])).
% 19.41/3.00  
% 19.41/3.00  fof(f1,axiom,(
% 19.41/3.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 19.41/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.41/3.00  
% 19.41/3.00  fof(f55,plain,(
% 19.41/3.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 19.41/3.00    inference(cnf_transformation,[],[f1])).
% 19.41/3.00  
% 19.41/3.00  fof(f6,axiom,(
% 19.41/3.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 19.41/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.41/3.00  
% 19.41/3.00  fof(f60,plain,(
% 19.41/3.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 19.41/3.00    inference(cnf_transformation,[],[f6])).
% 19.41/3.00  
% 19.41/3.00  fof(f93,plain,(
% 19.41/3.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 19.41/3.00    inference(definition_unfolding,[],[f55,f60,f60])).
% 19.41/3.00  
% 19.41/3.00  fof(f17,conjecture,(
% 19.41/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 19.41/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.41/3.00  
% 19.41/3.00  fof(f18,negated_conjecture,(
% 19.41/3.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 19.41/3.00    inference(negated_conjecture,[],[f17])).
% 19.41/3.00  
% 19.41/3.00  fof(f20,plain,(
% 19.41/3.00    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 19.41/3.00    inference(pure_predicate_removal,[],[f18])).
% 19.41/3.00  
% 19.41/3.00  fof(f34,plain,(
% 19.41/3.00    ? [X0] : (? [X1] : (? [X2] : (((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 19.41/3.00    inference(ennf_transformation,[],[f20])).
% 19.41/3.00  
% 19.41/3.00  fof(f35,plain,(
% 19.41/3.00    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 19.41/3.00    inference(flattening,[],[f34])).
% 19.41/3.00  
% 19.41/3.00  fof(f53,plain,(
% 19.41/3.00    ( ! [X0,X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ((r1_tsep_1(sK8,X1) | r1_tsep_1(X1,sK8)) & m1_pre_topc(X1,sK8) & m1_pre_topc(sK8,X0) & ~v2_struct_0(sK8))) )),
% 19.41/3.00    introduced(choice_axiom,[])).
% 19.41/3.00  
% 19.41/3.00  fof(f52,plain,(
% 19.41/3.00    ( ! [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : ((r1_tsep_1(X2,sK7) | r1_tsep_1(sK7,X2)) & m1_pre_topc(sK7,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK7,X0) & ~v2_struct_0(sK7))) )),
% 19.41/3.00    introduced(choice_axiom,[])).
% 19.41/3.00  
% 19.41/3.00  fof(f51,plain,(
% 19.41/3.00    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,sK6) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK6) & ~v2_struct_0(X1)) & l1_pre_topc(sK6) & ~v2_struct_0(sK6))),
% 19.41/3.00    introduced(choice_axiom,[])).
% 19.41/3.00  
% 19.41/3.00  fof(f54,plain,(
% 19.41/3.00    (((r1_tsep_1(sK8,sK7) | r1_tsep_1(sK7,sK8)) & m1_pre_topc(sK7,sK8) & m1_pre_topc(sK8,sK6) & ~v2_struct_0(sK8)) & m1_pre_topc(sK7,sK6) & ~v2_struct_0(sK7)) & l1_pre_topc(sK6) & ~v2_struct_0(sK6)),
% 19.41/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f35,f53,f52,f51])).
% 19.41/3.00  
% 19.41/3.00  fof(f91,plain,(
% 19.41/3.00    m1_pre_topc(sK7,sK8)),
% 19.41/3.00    inference(cnf_transformation,[],[f54])).
% 19.41/3.00  
% 19.41/3.00  fof(f11,axiom,(
% 19.41/3.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 19.41/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.41/3.00  
% 19.41/3.00  fof(f26,plain,(
% 19.41/3.00    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 19.41/3.00    inference(ennf_transformation,[],[f11])).
% 19.41/3.00  
% 19.41/3.00  fof(f37,plain,(
% 19.41/3.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 19.41/3.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 19.41/3.00  
% 19.41/3.00  fof(f36,plain,(
% 19.41/3.00    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 19.41/3.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 19.41/3.00  
% 19.41/3.00  fof(f38,plain,(
% 19.41/3.00    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 19.41/3.00    inference(definition_folding,[],[f26,f37,f36])).
% 19.41/3.00  
% 19.41/3.00  fof(f78,plain,(
% 19.41/3.00    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 19.41/3.00    inference(cnf_transformation,[],[f38])).
% 19.41/3.00  
% 19.41/3.00  fof(f42,plain,(
% 19.41/3.00    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 19.41/3.00    inference(nnf_transformation,[],[f37])).
% 19.41/3.00  
% 19.41/3.00  fof(f66,plain,(
% 19.41/3.00    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 19.41/3.00    inference(cnf_transformation,[],[f42])).
% 19.41/3.00  
% 19.41/3.00  fof(f13,axiom,(
% 19.41/3.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 19.41/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.41/3.00  
% 19.41/3.00  fof(f28,plain,(
% 19.41/3.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 19.41/3.00    inference(ennf_transformation,[],[f13])).
% 19.41/3.00  
% 19.41/3.00  fof(f80,plain,(
% 19.41/3.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 19.41/3.00    inference(cnf_transformation,[],[f28])).
% 19.41/3.00  
% 19.41/3.00  fof(f86,plain,(
% 19.41/3.00    l1_pre_topc(sK6)),
% 19.41/3.00    inference(cnf_transformation,[],[f54])).
% 19.41/3.00  
% 19.41/3.00  fof(f90,plain,(
% 19.41/3.00    m1_pre_topc(sK8,sK6)),
% 19.41/3.00    inference(cnf_transformation,[],[f54])).
% 19.41/3.00  
% 19.41/3.00  fof(f43,plain,(
% 19.41/3.00    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 19.41/3.00    inference(nnf_transformation,[],[f36])).
% 19.41/3.00  
% 19.41/3.00  fof(f44,plain,(
% 19.41/3.00    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 19.41/3.00    inference(flattening,[],[f43])).
% 19.41/3.00  
% 19.41/3.00  fof(f45,plain,(
% 19.41/3.00    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 19.41/3.00    inference(rectify,[],[f44])).
% 19.41/3.00  
% 19.41/3.00  fof(f48,plain,(
% 19.41/3.00    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 19.41/3.00    introduced(choice_axiom,[])).
% 19.41/3.00  
% 19.41/3.00  fof(f47,plain,(
% 19.41/3.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 19.41/3.00    introduced(choice_axiom,[])).
% 19.41/3.00  
% 19.41/3.00  fof(f46,plain,(
% 19.41/3.00    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK3(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK3(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK3(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK3(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 19.41/3.00    introduced(choice_axiom,[])).
% 19.41/3.00  
% 19.41/3.00  fof(f49,plain,(
% 19.41/3.00    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK3(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK3(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1),k2_struct_0(X0)) = sK3(X0,X1) & r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK3(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 19.41/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f45,f48,f47,f46])).
% 19.41/3.00  
% 19.41/3.00  fof(f68,plain,(
% 19.41/3.00    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 19.41/3.00    inference(cnf_transformation,[],[f49])).
% 19.41/3.00  
% 19.41/3.00  fof(f4,axiom,(
% 19.41/3.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 19.41/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.41/3.00  
% 19.41/3.00  fof(f23,plain,(
% 19.41/3.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 19.41/3.00    inference(ennf_transformation,[],[f4])).
% 19.41/3.00  
% 19.41/3.00  fof(f58,plain,(
% 19.41/3.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 19.41/3.00    inference(cnf_transformation,[],[f23])).
% 19.41/3.00  
% 19.41/3.00  fof(f94,plain,(
% 19.41/3.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 19.41/3.00    inference(definition_unfolding,[],[f58,f60])).
% 19.41/3.00  
% 19.41/3.00  fof(f92,plain,(
% 19.41/3.00    r1_tsep_1(sK8,sK7) | r1_tsep_1(sK7,sK8)),
% 19.41/3.00    inference(cnf_transformation,[],[f54])).
% 19.41/3.00  
% 19.41/3.00  fof(f12,axiom,(
% 19.41/3.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 19.41/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.41/3.00  
% 19.41/3.00  fof(f27,plain,(
% 19.41/3.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 19.41/3.00    inference(ennf_transformation,[],[f12])).
% 19.41/3.00  
% 19.41/3.00  fof(f79,plain,(
% 19.41/3.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 19.41/3.00    inference(cnf_transformation,[],[f27])).
% 19.41/3.00  
% 19.41/3.00  fof(f16,axiom,(
% 19.41/3.00    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 19.41/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.41/3.00  
% 19.41/3.00  fof(f32,plain,(
% 19.41/3.00    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 19.41/3.00    inference(ennf_transformation,[],[f16])).
% 19.41/3.00  
% 19.41/3.00  fof(f33,plain,(
% 19.41/3.00    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 19.41/3.00    inference(flattening,[],[f32])).
% 19.41/3.00  
% 19.41/3.00  fof(f84,plain,(
% 19.41/3.00    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 19.41/3.00    inference(cnf_transformation,[],[f33])).
% 19.41/3.00  
% 19.41/3.00  fof(f15,axiom,(
% 19.41/3.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 19.41/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.41/3.00  
% 19.41/3.00  fof(f31,plain,(
% 19.41/3.00    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 19.41/3.00    inference(ennf_transformation,[],[f15])).
% 19.41/3.00  
% 19.41/3.00  fof(f50,plain,(
% 19.41/3.00    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 19.41/3.00    inference(nnf_transformation,[],[f31])).
% 19.41/3.00  
% 19.41/3.00  fof(f82,plain,(
% 19.41/3.00    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 19.41/3.00    inference(cnf_transformation,[],[f50])).
% 19.41/3.00  
% 19.41/3.00  fof(f10,axiom,(
% 19.41/3.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 19.41/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.41/3.00  
% 19.41/3.00  fof(f25,plain,(
% 19.41/3.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 19.41/3.00    inference(ennf_transformation,[],[f10])).
% 19.41/3.00  
% 19.41/3.00  fof(f65,plain,(
% 19.41/3.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 19.41/3.00    inference(cnf_transformation,[],[f25])).
% 19.41/3.00  
% 19.41/3.00  fof(f9,axiom,(
% 19.41/3.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 19.41/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.41/3.00  
% 19.41/3.00  fof(f24,plain,(
% 19.41/3.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 19.41/3.00    inference(ennf_transformation,[],[f9])).
% 19.41/3.00  
% 19.41/3.00  fof(f64,plain,(
% 19.41/3.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 19.41/3.00    inference(cnf_transformation,[],[f24])).
% 19.41/3.00  
% 19.41/3.00  fof(f5,axiom,(
% 19.41/3.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 19.41/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.41/3.00  
% 19.41/3.00  fof(f59,plain,(
% 19.41/3.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 19.41/3.00    inference(cnf_transformation,[],[f5])).
% 19.41/3.00  
% 19.41/3.00  fof(f2,axiom,(
% 19.41/3.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 19.41/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.41/3.00  
% 19.41/3.00  fof(f19,plain,(
% 19.41/3.00    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 19.41/3.00    inference(unused_predicate_definition_removal,[],[f2])).
% 19.41/3.00  
% 19.41/3.00  fof(f21,plain,(
% 19.41/3.00    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 19.41/3.00    inference(ennf_transformation,[],[f19])).
% 19.41/3.00  
% 19.41/3.00  fof(f39,plain,(
% 19.41/3.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 19.41/3.00    introduced(choice_axiom,[])).
% 19.41/3.00  
% 19.41/3.00  fof(f40,plain,(
% 19.41/3.00    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK2(X0),X0))),
% 19.41/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f39])).
% 19.41/3.00  
% 19.41/3.00  fof(f56,plain,(
% 19.41/3.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) )),
% 19.41/3.00    inference(cnf_transformation,[],[f40])).
% 19.41/3.00  
% 19.41/3.00  fof(f14,axiom,(
% 19.41/3.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 19.41/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.41/3.00  
% 19.41/3.00  fof(f29,plain,(
% 19.41/3.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 19.41/3.00    inference(ennf_transformation,[],[f14])).
% 19.41/3.00  
% 19.41/3.00  fof(f30,plain,(
% 19.41/3.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 19.41/3.00    inference(flattening,[],[f29])).
% 19.41/3.00  
% 19.41/3.00  fof(f81,plain,(
% 19.41/3.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 19.41/3.00    inference(cnf_transformation,[],[f30])).
% 19.41/3.00  
% 19.41/3.00  fof(f87,plain,(
% 19.41/3.00    ~v2_struct_0(sK7)),
% 19.41/3.00    inference(cnf_transformation,[],[f54])).
% 19.41/3.00  
% 19.41/3.00  cnf(c_5,plain,
% 19.41/3.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 19.41/3.00      inference(cnf_transformation,[],[f61]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_47684,plain,
% 19.41/3.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_2,plain,
% 19.41/3.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 19.41/3.00      inference(cnf_transformation,[],[f57]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_47687,plain,
% 19.41/3.00      ( r1_xboole_0(X0,X1) != iProver_top
% 19.41/3.00      | r1_xboole_0(X1,X0) = iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_48683,plain,
% 19.41/3.00      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_47684,c_47687]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_7,plain,
% 19.41/3.00      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 19.41/3.00      inference(cnf_transformation,[],[f62]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_47683,plain,
% 19.41/3.00      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_48783,plain,
% 19.41/3.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_48683,c_47683]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_48488,plain,
% 19.41/3.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_47684,c_47683]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_0,plain,
% 19.41/3.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.41/3.00      inference(cnf_transformation,[],[f93]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_48490,plain,
% 19.41/3.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_48488,c_0]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_49913,plain,
% 19.41/3.00      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 19.41/3.00      inference(demodulation,[status(thm)],[c_48783,c_48490]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_49914,plain,
% 19.41/3.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.41/3.00      inference(demodulation,[status(thm)],[c_49913,c_48783]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_30,negated_conjecture,
% 19.41/3.00      ( m1_pre_topc(sK7,sK8) ),
% 19.41/3.00      inference(cnf_transformation,[],[f91]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_47672,plain,
% 19.41/3.00      ( m1_pre_topc(sK7,sK8) = iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_22,plain,
% 19.41/3.00      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 19.41/3.00      inference(cnf_transformation,[],[f78]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_47678,plain,
% 19.41/3.00      ( sP1(X0,X1) = iProver_top
% 19.41/3.00      | l1_pre_topc(X1) != iProver_top
% 19.41/3.00      | l1_pre_topc(X0) != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_11,plain,
% 19.41/3.00      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 19.41/3.00      inference(cnf_transformation,[],[f66]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_47680,plain,
% 19.41/3.00      ( sP1(X0,X1) != iProver_top
% 19.41/3.00      | sP0(X1,X0) = iProver_top
% 19.41/3.00      | m1_pre_topc(X1,X0) != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_49910,plain,
% 19.41/3.00      ( sP0(X0,X1) = iProver_top
% 19.41/3.00      | m1_pre_topc(X0,X1) != iProver_top
% 19.41/3.00      | l1_pre_topc(X1) != iProver_top
% 19.41/3.00      | l1_pre_topc(X0) != iProver_top ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_47678,c_47680]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_3974,plain,
% 19.41/3.00      ( sP0(X0,X1)
% 19.41/3.00      | ~ m1_pre_topc(X0,X1)
% 19.41/3.00      | ~ l1_pre_topc(X1)
% 19.41/3.00      | ~ l1_pre_topc(X0) ),
% 19.41/3.00      inference(resolution,[status(thm)],[c_11,c_22]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_24,plain,
% 19.41/3.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 19.41/3.00      inference(cnf_transformation,[],[f80]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_4015,plain,
% 19.41/3.00      ( ~ l1_pre_topc(X1) | ~ m1_pre_topc(X0,X1) | sP0(X0,X1) ),
% 19.41/3.00      inference(global_propositional_subsumption,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_3974,c_24]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_4016,plain,
% 19.41/3.00      ( sP0(X0,X1) | ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) ),
% 19.41/3.00      inference(renaming,[status(thm)],[c_4015]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_4017,plain,
% 19.41/3.00      ( sP0(X0,X1) = iProver_top
% 19.41/3.00      | m1_pre_topc(X0,X1) != iProver_top
% 19.41/3.00      | l1_pre_topc(X1) != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_4016]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_55718,plain,
% 19.41/3.00      ( l1_pre_topc(X1) != iProver_top
% 19.41/3.00      | m1_pre_topc(X0,X1) != iProver_top
% 19.41/3.00      | sP0(X0,X1) = iProver_top ),
% 19.41/3.00      inference(global_propositional_subsumption,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_49910,c_4017]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_55719,plain,
% 19.41/3.00      ( sP0(X0,X1) = iProver_top
% 19.41/3.00      | m1_pre_topc(X0,X1) != iProver_top
% 19.41/3.00      | l1_pre_topc(X1) != iProver_top ),
% 19.41/3.00      inference(renaming,[status(thm)],[c_55718]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_55725,plain,
% 19.41/3.00      ( sP0(sK7,sK8) = iProver_top | l1_pre_topc(sK8) != iProver_top ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_47672,c_55719]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_35,negated_conjecture,
% 19.41/3.00      ( l1_pre_topc(sK6) ),
% 19.41/3.00      inference(cnf_transformation,[],[f86]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_38,plain,
% 19.41/3.00      ( l1_pre_topc(sK6) = iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_43,plain,
% 19.41/3.00      ( m1_pre_topc(sK7,sK8) = iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_3652,plain,
% 19.41/3.00      ( ~ sP1(sK8,sK7) | sP0(sK7,sK8) | ~ m1_pre_topc(sK7,sK8) ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_11]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_3653,plain,
% 19.41/3.00      ( sP1(sK8,sK7) != iProver_top
% 19.41/3.00      | sP0(sK7,sK8) = iProver_top
% 19.41/3.00      | m1_pre_topc(sK7,sK8) != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_3652]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_3665,plain,
% 19.41/3.00      ( sP1(sK8,sK7) | ~ l1_pre_topc(sK7) | ~ l1_pre_topc(sK8) ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_22]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_3666,plain,
% 19.41/3.00      ( sP1(sK8,sK7) = iProver_top
% 19.41/3.00      | l1_pre_topc(sK7) != iProver_top
% 19.41/3.00      | l1_pre_topc(sK8) != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_3665]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_3713,plain,
% 19.41/3.00      ( l1_pre_topc(sK7) | ~ l1_pre_topc(sK8) ),
% 19.41/3.00      inference(resolution,[status(thm)],[c_24,c_30]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_3714,plain,
% 19.41/3.00      ( l1_pre_topc(sK7) = iProver_top
% 19.41/3.00      | l1_pre_topc(sK8) != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_3713]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_31,negated_conjecture,
% 19.41/3.00      ( m1_pre_topc(sK8,sK6) ),
% 19.41/3.00      inference(cnf_transformation,[],[f90]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_3715,plain,
% 19.41/3.00      ( ~ l1_pre_topc(sK6) | l1_pre_topc(sK8) ),
% 19.41/3.00      inference(resolution,[status(thm)],[c_24,c_31]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_3716,plain,
% 19.41/3.00      ( l1_pre_topc(sK6) != iProver_top
% 19.41/3.00      | l1_pre_topc(sK8) = iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_3715]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_55969,plain,
% 19.41/3.00      ( sP0(sK7,sK8) = iProver_top ),
% 19.41/3.00      inference(global_propositional_subsumption,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_55725,c_38,c_43,c_3653,c_3666,c_3714,c_3716]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_21,plain,
% 19.41/3.00      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 19.41/3.00      inference(cnf_transformation,[],[f68]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_47679,plain,
% 19.41/3.00      ( sP0(X0,X1) != iProver_top
% 19.41/3.00      | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) = iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_3,plain,
% 19.41/3.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 19.41/3.00      inference(cnf_transformation,[],[f94]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_47686,plain,
% 19.41/3.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 19.41/3.00      | r1_tarski(X0,X1) != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_49021,plain,
% 19.41/3.00      ( k4_xboole_0(k2_struct_0(X0),k4_xboole_0(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0)
% 19.41/3.00      | sP0(X0,X1) != iProver_top ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_47679,c_47686]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_56344,plain,
% 19.41/3.00      ( k4_xboole_0(k2_struct_0(sK7),k4_xboole_0(k2_struct_0(sK7),k2_struct_0(sK8))) = k2_struct_0(sK7) ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_55969,c_49021]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_29,negated_conjecture,
% 19.41/3.00      ( r1_tsep_1(sK7,sK8) | r1_tsep_1(sK8,sK7) ),
% 19.41/3.00      inference(cnf_transformation,[],[f92]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_23,plain,
% 19.41/3.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 19.41/3.00      inference(cnf_transformation,[],[f79]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_57,plain,
% 19.41/3.00      ( ~ l1_pre_topc(sK7) | l1_struct_0(sK7) ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_23]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_3756,plain,
% 19.41/3.00      ( l1_pre_topc(sK8) ),
% 19.41/3.00      inference(global_propositional_subsumption,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_3715,c_35]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_3816,plain,
% 19.41/3.00      ( l1_struct_0(sK8) ),
% 19.41/3.00      inference(resolution,[status(thm)],[c_3756,c_23]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_28,plain,
% 19.41/3.00      ( ~ r1_tsep_1(X0,X1)
% 19.41/3.00      | r1_tsep_1(X1,X0)
% 19.41/3.00      | ~ l1_struct_0(X0)
% 19.41/3.00      | ~ l1_struct_0(X1) ),
% 19.41/3.00      inference(cnf_transformation,[],[f84]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_23215,plain,
% 19.41/3.00      ( r1_tsep_1(sK7,sK8)
% 19.41/3.00      | ~ r1_tsep_1(sK8,sK7)
% 19.41/3.00      | ~ l1_struct_0(sK7)
% 19.41/3.00      | ~ l1_struct_0(sK8) ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_28]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_23248,plain,
% 19.41/3.00      ( ~ r1_tsep_1(sK7,sK8)
% 19.41/3.00      | r1_tsep_1(sK8,sK7)
% 19.41/3.00      | ~ l1_struct_0(sK7)
% 19.41/3.00      | ~ l1_struct_0(sK8) ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_28]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_47559,negated_conjecture,
% 19.41/3.00      ( r1_tsep_1(sK8,sK7) ),
% 19.41/3.00      inference(global_propositional_subsumption,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_29,c_35,c_57,c_3713,c_3715,c_3816,c_23215,c_23248]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_47665,plain,
% 19.41/3.00      ( r1_tsep_1(sK8,sK7) = iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_47559]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_47673,plain,
% 19.41/3.00      ( r1_tsep_1(X0,X1) != iProver_top
% 19.41/3.00      | r1_tsep_1(X1,X0) = iProver_top
% 19.41/3.00      | l1_struct_0(X0) != iProver_top
% 19.41/3.00      | l1_struct_0(X1) != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_48094,plain,
% 19.41/3.00      ( r1_tsep_1(sK7,sK8) = iProver_top
% 19.41/3.00      | l1_struct_0(sK7) != iProver_top
% 19.41/3.00      | l1_struct_0(sK8) != iProver_top ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_47665,c_47673]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_23227,negated_conjecture,
% 19.41/3.00      ( r1_tsep_1(sK7,sK8) ),
% 19.41/3.00      inference(global_propositional_subsumption,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_29,c_35,c_57,c_3713,c_3715,c_3816,c_23215]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_23229,plain,
% 19.41/3.00      ( r1_tsep_1(sK7,sK8) = iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_23227]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_48383,plain,
% 19.41/3.00      ( r1_tsep_1(sK7,sK8) = iProver_top ),
% 19.41/3.00      inference(global_propositional_subsumption,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_48094,c_23229]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_27,plain,
% 19.41/3.00      ( ~ r1_tsep_1(X0,X1)
% 19.41/3.00      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 19.41/3.00      | ~ l1_struct_0(X0)
% 19.41/3.00      | ~ l1_struct_0(X1) ),
% 19.41/3.00      inference(cnf_transformation,[],[f82]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_47674,plain,
% 19.41/3.00      ( r1_tsep_1(X0,X1) != iProver_top
% 19.41/3.00      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 19.41/3.00      | l1_struct_0(X0) != iProver_top
% 19.41/3.00      | l1_struct_0(X1) != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_48794,plain,
% 19.41/3.00      ( k4_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(X0)
% 19.41/3.00      | r1_tsep_1(X0,X1) != iProver_top
% 19.41/3.00      | l1_struct_0(X0) != iProver_top
% 19.41/3.00      | l1_struct_0(X1) != iProver_top ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_47674,c_47683]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_51952,plain,
% 19.41/3.00      ( k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) = u1_struct_0(sK7)
% 19.41/3.00      | l1_struct_0(sK7) != iProver_top
% 19.41/3.00      | l1_struct_0(sK8) != iProver_top ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_48383,c_48794]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_47676,plain,
% 19.41/3.00      ( m1_pre_topc(X0,X1) != iProver_top
% 19.41/3.00      | l1_pre_topc(X1) != iProver_top
% 19.41/3.00      | l1_pre_topc(X0) = iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_49772,plain,
% 19.41/3.00      ( l1_pre_topc(sK7) = iProver_top
% 19.41/3.00      | l1_pre_topc(sK8) != iProver_top ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_47672,c_47676]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_50160,plain,
% 19.41/3.00      ( l1_pre_topc(sK7) = iProver_top ),
% 19.41/3.00      inference(global_propositional_subsumption,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_49772,c_38,c_3714,c_3716]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_47677,plain,
% 19.41/3.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_50165,plain,
% 19.41/3.00      ( l1_struct_0(sK7) = iProver_top ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_50160,c_47677]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_9,plain,
% 19.41/3.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 19.41/3.00      inference(cnf_transformation,[],[f65]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_47681,plain,
% 19.41/3.00      ( u1_struct_0(X0) = k2_struct_0(X0)
% 19.41/3.00      | l1_struct_0(X0) != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_50277,plain,
% 19.41/3.00      ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_50165,c_47681]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_47671,plain,
% 19.41/3.00      ( m1_pre_topc(sK8,sK6) = iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_49773,plain,
% 19.41/3.00      ( l1_pre_topc(sK6) != iProver_top
% 19.41/3.00      | l1_pre_topc(sK8) = iProver_top ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_47671,c_47676]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_50263,plain,
% 19.41/3.00      ( l1_pre_topc(sK8) = iProver_top ),
% 19.41/3.00      inference(global_propositional_subsumption,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_49773,c_38,c_3716]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_50268,plain,
% 19.41/3.00      ( l1_struct_0(sK8) = iProver_top ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_50263,c_47677]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_50412,plain,
% 19.41/3.00      ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_50268,c_47681]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_51964,plain,
% 19.41/3.00      ( k4_xboole_0(k2_struct_0(sK7),k2_struct_0(sK8)) = k2_struct_0(sK7)
% 19.41/3.00      | l1_struct_0(sK7) != iProver_top
% 19.41/3.00      | l1_struct_0(sK8) != iProver_top ),
% 19.41/3.00      inference(light_normalisation,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_51952,c_50277,c_50412]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_99,plain,
% 19.41/3.00      ( ~ l1_struct_0(sK7) | u1_struct_0(sK7) = k2_struct_0(sK7) ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_9]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_402,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_6797,plain,
% 19.41/3.00      ( X0 != X1 | X0 = u1_struct_0(X2) | u1_struct_0(X2) != X1 ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_402]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_7010,plain,
% 19.41/3.00      ( X0 = u1_struct_0(X1)
% 19.41/3.00      | X0 != k2_struct_0(X1)
% 19.41/3.00      | u1_struct_0(X1) != k2_struct_0(X1) ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_6797]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_7017,plain,
% 19.41/3.00      ( u1_struct_0(X0) != k2_struct_0(X0)
% 19.41/3.00      | k2_struct_0(X0) = u1_struct_0(X0)
% 19.41/3.00      | k2_struct_0(X0) != k2_struct_0(X0) ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_7010]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_7018,plain,
% 19.41/3.00      ( u1_struct_0(X0) != k2_struct_0(X0)
% 19.41/3.00      | k2_struct_0(X0) = u1_struct_0(X0) ),
% 19.41/3.00      inference(equality_resolution_simp,[status(thm)],[c_7017]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_7019,plain,
% 19.41/3.00      ( u1_struct_0(sK7) != k2_struct_0(sK7)
% 19.41/3.00      | k2_struct_0(sK7) = u1_struct_0(sK7) ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_7018]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_5663,negated_conjecture,
% 19.41/3.00      ( arAF0_m1_pre_topc_0_1(sK8) | ~ iProver_ARSWP_115 ),
% 19.41/3.00      inference(arg_filter_abstr,[status(unp)],[c_31]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_6280,plain,
% 19.41/3.00      ( arAF0_m1_pre_topc_0_1(sK8) = iProver_top
% 19.41/3.00      | iProver_ARSWP_115 != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_5663]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_5657,plain,
% 19.41/3.00      ( ~ arAF0_m1_pre_topc_0_1(X0)
% 19.41/3.00      | ~ l1_pre_topc(X1)
% 19.41/3.00      | l1_pre_topc(X0)
% 19.41/3.00      | ~ iProver_ARSWP_109 ),
% 19.41/3.00      inference(arg_filter_abstr,[status(unp)],[c_24]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_6285,plain,
% 19.41/3.00      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 19.41/3.00      | l1_pre_topc(X1) != iProver_top
% 19.41/3.00      | l1_pre_topc(X0) = iProver_top
% 19.41/3.00      | iProver_ARSWP_109 != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_5657]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_6770,plain,
% 19.41/3.00      ( ~ arAF0_m1_pre_topc_0_1(X0)
% 19.41/3.00      | l1_pre_topc(X0)
% 19.41/3.00      | ~ iProver_ARSWP_109 ),
% 19.41/3.00      inference(resolution,[status(thm)],[c_5657,c_35]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_6771,plain,
% 19.41/3.00      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 19.41/3.00      | l1_pre_topc(X0) = iProver_top
% 19.41/3.00      | iProver_ARSWP_109 != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_6770]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_6820,plain,
% 19.41/3.00      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 19.41/3.00      | l1_pre_topc(X0) = iProver_top
% 19.41/3.00      | iProver_ARSWP_109 != iProver_top ),
% 19.41/3.00      inference(global_propositional_subsumption,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_6285,c_6771]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_6828,plain,
% 19.41/3.00      ( l1_pre_topc(sK8) = iProver_top
% 19.41/3.00      | iProver_ARSWP_115 != iProver_top
% 19.41/3.00      | iProver_ARSWP_109 != iProver_top ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_6280,c_6820]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_7227,plain,
% 19.41/3.00      ( l1_pre_topc(sK8) = iProver_top ),
% 19.41/3.00      inference(global_propositional_subsumption,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_6828,c_38,c_3716]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_6314,plain,
% 19.41/3.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_7232,plain,
% 19.41/3.00      ( l1_struct_0(sK8) = iProver_top ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_7227,c_6314]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_6315,plain,
% 19.41/3.00      ( u1_struct_0(X0) = k2_struct_0(X0)
% 19.41/3.00      | l1_struct_0(X0) != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_7377,plain,
% 19.41/3.00      ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_7232,c_6315]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_10772,plain,
% 19.41/3.00      ( ~ r1_tsep_1(sK7,sK8)
% 19.41/3.00      | r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))
% 19.41/3.00      | ~ l1_struct_0(sK7)
% 19.41/3.00      | ~ l1_struct_0(sK8) ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_27]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_25440,plain,
% 19.41/3.00      ( X0 != X1 | X0 = u1_struct_0(sK8) | u1_struct_0(sK8) != X1 ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_402]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_25570,plain,
% 19.41/3.00      ( X0 = u1_struct_0(sK8)
% 19.41/3.00      | X0 != k2_struct_0(sK8)
% 19.41/3.00      | u1_struct_0(sK8) != k2_struct_0(sK8) ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_25440]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_25627,plain,
% 19.41/3.00      ( u1_struct_0(sK8) != k2_struct_0(sK8)
% 19.41/3.00      | k2_struct_0(sK8) = u1_struct_0(sK8)
% 19.41/3.00      | k2_struct_0(sK8) != k2_struct_0(sK8) ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_25570]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_25628,plain,
% 19.41/3.00      ( u1_struct_0(sK8) != k2_struct_0(sK8)
% 19.41/3.00      | k2_struct_0(sK8) = u1_struct_0(sK8) ),
% 19.41/3.00      inference(equality_resolution_simp,[status(thm)],[c_25627]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_406,plain,
% 19.41/3.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.41/3.00      theory(equality) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_25383,plain,
% 19.41/3.00      ( r1_xboole_0(X0,X1)
% 19.41/3.00      | ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))
% 19.41/3.00      | X0 != u1_struct_0(sK7)
% 19.41/3.00      | X1 != u1_struct_0(sK8) ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_406]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_25557,plain,
% 19.41/3.00      ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))
% 19.41/3.00      | r1_xboole_0(k2_struct_0(sK7),X0)
% 19.41/3.00      | X0 != u1_struct_0(sK8)
% 19.41/3.00      | k2_struct_0(sK7) != u1_struct_0(sK7) ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_25383]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_26728,plain,
% 19.41/3.00      ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))
% 19.41/3.00      | r1_xboole_0(k2_struct_0(sK7),k2_struct_0(sK8))
% 19.41/3.00      | k2_struct_0(sK7) != u1_struct_0(sK7)
% 19.41/3.00      | k2_struct_0(sK8) != u1_struct_0(sK8) ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_25557]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_31434,plain,
% 19.41/3.00      ( ~ r1_xboole_0(k2_struct_0(sK7),k2_struct_0(sK8))
% 19.41/3.00      | k4_xboole_0(k2_struct_0(sK7),k2_struct_0(sK8)) = k2_struct_0(sK7) ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_7]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_52599,plain,
% 19.41/3.00      ( k4_xboole_0(k2_struct_0(sK7),k2_struct_0(sK8)) = k2_struct_0(sK7) ),
% 19.41/3.00      inference(global_propositional_subsumption,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_51964,c_35,c_29,c_57,c_99,c_3713,c_3715,c_3816,c_7019,
% 19.41/3.00                 c_7377,c_10772,c_23215,c_25628,c_26728,c_31434]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_52602,plain,
% 19.41/3.00      ( k4_xboole_0(k2_struct_0(sK8),k4_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))) = k4_xboole_0(k2_struct_0(sK7),k2_struct_0(sK7)) ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_52599,c_0]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_51953,plain,
% 19.41/3.00      ( k4_xboole_0(u1_struct_0(sK8),u1_struct_0(sK7)) = u1_struct_0(sK8)
% 19.41/3.00      | l1_struct_0(sK7) != iProver_top
% 19.41/3.00      | l1_struct_0(sK8) != iProver_top ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_47665,c_48794]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_51957,plain,
% 19.41/3.00      ( k4_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) = k2_struct_0(sK8)
% 19.41/3.00      | l1_struct_0(sK7) != iProver_top
% 19.41/3.00      | l1_struct_0(sK8) != iProver_top ),
% 19.41/3.00      inference(light_normalisation,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_51953,c_50277,c_50412]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_23844,negated_conjecture,
% 19.41/3.00      ( arAF0_m1_pre_topc_0_1(sK8) | ~ iProver_ARSWP_171 ),
% 19.41/3.00      inference(arg_filter_abstr,[status(unp)],[c_31]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_24650,plain,
% 19.41/3.00      ( arAF0_m1_pre_topc_0_1(sK8) = iProver_top
% 19.41/3.00      | iProver_ARSWP_171 != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_23844]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_23842,plain,
% 19.41/3.00      ( ~ arAF0_m1_pre_topc_0_1(X0)
% 19.41/3.00      | ~ l1_pre_topc(X1)
% 19.41/3.00      | l1_pre_topc(X0)
% 19.41/3.00      | ~ iProver_ARSWP_169 ),
% 19.41/3.00      inference(arg_filter_abstr,[status(unp)],[c_24]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_24652,plain,
% 19.41/3.00      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 19.41/3.00      | l1_pre_topc(X1) != iProver_top
% 19.41/3.00      | l1_pre_topc(X0) = iProver_top
% 19.41/3.00      | iProver_ARSWP_169 != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_23842]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_25191,plain,
% 19.41/3.00      ( ~ arAF0_m1_pre_topc_0_1(X0)
% 19.41/3.00      | l1_pre_topc(X0)
% 19.41/3.00      | ~ iProver_ARSWP_169 ),
% 19.41/3.00      inference(resolution,[status(thm)],[c_23842,c_35]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_25192,plain,
% 19.41/3.00      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 19.41/3.00      | l1_pre_topc(X0) = iProver_top
% 19.41/3.00      | iProver_ARSWP_169 != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_25191]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_25248,plain,
% 19.41/3.00      ( arAF0_m1_pre_topc_0_1(X0) != iProver_top
% 19.41/3.00      | l1_pre_topc(X0) = iProver_top
% 19.41/3.00      | iProver_ARSWP_169 != iProver_top ),
% 19.41/3.00      inference(global_propositional_subsumption,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_24652,c_25192]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_25256,plain,
% 19.41/3.00      ( l1_pre_topc(sK8) = iProver_top
% 19.41/3.00      | iProver_ARSWP_171 != iProver_top
% 19.41/3.00      | iProver_ARSWP_169 != iProver_top ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_24650,c_25248]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_25600,plain,
% 19.41/3.00      ( l1_pre_topc(sK8) = iProver_top ),
% 19.41/3.00      inference(global_propositional_subsumption,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_25256,c_38,c_3716]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_24681,plain,
% 19.41/3.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_25605,plain,
% 19.41/3.00      ( l1_struct_0(sK8) = iProver_top ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_25600,c_24681]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_24682,plain,
% 19.41/3.00      ( u1_struct_0(X0) = k2_struct_0(X0)
% 19.41/3.00      | l1_struct_0(X0) != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_25724,plain,
% 19.41/3.00      ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_25605,c_24682]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_23843,negated_conjecture,
% 19.41/3.00      ( arAF0_m1_pre_topc_0_1(sK7) | ~ iProver_ARSWP_170 ),
% 19.41/3.00      inference(arg_filter_abstr,[status(unp)],[c_30]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_24651,plain,
% 19.41/3.00      ( arAF0_m1_pre_topc_0_1(sK7) = iProver_top
% 19.41/3.00      | iProver_ARSWP_170 != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_23843]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_25255,plain,
% 19.41/3.00      ( l1_pre_topc(sK7) = iProver_top
% 19.41/3.00      | iProver_ARSWP_170 != iProver_top
% 19.41/3.00      | iProver_ARSWP_169 != iProver_top ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_24651,c_25248]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_25592,plain,
% 19.41/3.00      ( l1_pre_topc(sK7) = iProver_top ),
% 19.41/3.00      inference(global_propositional_subsumption,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_25255,c_38,c_3714,c_3716]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_25597,plain,
% 19.41/3.00      ( l1_struct_0(sK7) = iProver_top ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_25592,c_24681]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_25721,plain,
% 19.41/3.00      ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_25597,c_24682]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_24678,plain,
% 19.41/3.00      ( r1_tsep_1(X0,X1) != iProver_top
% 19.41/3.00      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 19.41/3.00      | l1_struct_0(X0) != iProver_top
% 19.41/3.00      | l1_struct_0(X1) != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_27931,plain,
% 19.41/3.00      ( r1_tsep_1(sK7,X0) != iProver_top
% 19.41/3.00      | r1_xboole_0(k2_struct_0(sK7),u1_struct_0(X0)) = iProver_top
% 19.41/3.00      | l1_struct_0(X0) != iProver_top
% 19.41/3.00      | l1_struct_0(sK7) != iProver_top ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_25721,c_24678]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_56,plain,
% 19.41/3.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_58,plain,
% 19.41/3.00      ( l1_pre_topc(sK7) != iProver_top
% 19.41/3.00      | l1_struct_0(sK7) = iProver_top ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_56]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_29308,plain,
% 19.41/3.00      ( l1_struct_0(X0) != iProver_top
% 19.41/3.00      | r1_xboole_0(k2_struct_0(sK7),u1_struct_0(X0)) = iProver_top
% 19.41/3.00      | r1_tsep_1(sK7,X0) != iProver_top ),
% 19.41/3.00      inference(global_propositional_subsumption,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_27931,c_38,c_58,c_3714,c_3716]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_29309,plain,
% 19.41/3.00      ( r1_tsep_1(sK7,X0) != iProver_top
% 19.41/3.00      | r1_xboole_0(k2_struct_0(sK7),u1_struct_0(X0)) = iProver_top
% 19.41/3.00      | l1_struct_0(X0) != iProver_top ),
% 19.41/3.00      inference(renaming,[status(thm)],[c_29308]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_29317,plain,
% 19.41/3.00      ( r1_tsep_1(sK7,sK8) != iProver_top
% 19.41/3.00      | r1_xboole_0(k2_struct_0(sK7),k2_struct_0(sK8)) = iProver_top
% 19.41/3.00      | l1_struct_0(sK8) != iProver_top ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_25724,c_29309]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_3817,plain,
% 19.41/3.00      ( l1_struct_0(sK8) = iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_3816]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_10773,plain,
% 19.41/3.00      ( r1_tsep_1(sK7,sK8) != iProver_top
% 19.41/3.00      | r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) = iProver_top
% 19.41/3.00      | l1_struct_0(sK7) != iProver_top
% 19.41/3.00      | l1_struct_0(sK8) != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_10772]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_26729,plain,
% 19.41/3.00      ( k2_struct_0(sK7) != u1_struct_0(sK7)
% 19.41/3.00      | k2_struct_0(sK8) != u1_struct_0(sK8)
% 19.41/3.00      | r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) != iProver_top
% 19.41/3.00      | r1_xboole_0(k2_struct_0(sK7),k2_struct_0(sK8)) = iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_26728]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_32980,plain,
% 19.41/3.00      ( r1_xboole_0(k2_struct_0(sK7),k2_struct_0(sK8)) = iProver_top ),
% 19.41/3.00      inference(global_propositional_subsumption,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_29317,c_35,c_38,c_57,c_58,c_99,c_3713,c_3714,c_3715,
% 19.41/3.00                 c_3716,c_3817,c_7019,c_7377,c_10773,c_23229,c_25628,
% 19.41/3.00                 c_26729]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_24689,plain,
% 19.41/3.00      ( r1_xboole_0(X0,X1) != iProver_top
% 19.41/3.00      | r1_xboole_0(X1,X0) = iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_32985,plain,
% 19.41/3.00      ( r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) = iProver_top ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_32980,c_24689]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_24684,plain,
% 19.41/3.00      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 19.41/3.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_35025,plain,
% 19.41/3.00      ( k4_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) = k2_struct_0(sK8) ),
% 19.41/3.00      inference(superposition,[status(thm)],[c_32985,c_24684]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_52335,plain,
% 19.41/3.00      ( k4_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) = k2_struct_0(sK8) ),
% 19.41/3.00      inference(global_propositional_subsumption,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_51957,c_35025]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_52604,plain,
% 19.41/3.00      ( k4_xboole_0(k2_struct_0(sK8),k2_struct_0(sK8)) = k4_xboole_0(k2_struct_0(sK7),k2_struct_0(sK7)) ),
% 19.41/3.00      inference(light_normalisation,[status(thm)],[c_52602,c_52335]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_56352,plain,
% 19.41/3.00      ( k4_xboole_0(k2_struct_0(sK8),k2_struct_0(sK8)) = k2_struct_0(sK7) ),
% 19.41/3.00      inference(light_normalisation,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_56344,c_52599,c_52604]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_57276,plain,
% 19.41/3.00      ( k2_struct_0(sK7) = k1_xboole_0 ),
% 19.41/3.00      inference(demodulation,[status(thm)],[c_49914,c_56352]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_404,plain,
% 19.41/3.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 19.41/3.00      theory(equality) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_6777,plain,
% 19.41/3.00      ( ~ v1_xboole_0(X0)
% 19.41/3.00      | v1_xboole_0(k2_struct_0(X1))
% 19.41/3.00      | k2_struct_0(X1) != X0 ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_404]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_8593,plain,
% 19.41/3.00      ( v1_xboole_0(k2_struct_0(X0))
% 19.41/3.00      | ~ v1_xboole_0(k1_xboole_0)
% 19.41/3.00      | k2_struct_0(X0) != k1_xboole_0 ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_6777]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_8595,plain,
% 19.41/3.00      ( v1_xboole_0(k2_struct_0(sK7))
% 19.41/3.00      | ~ v1_xboole_0(k1_xboole_0)
% 19.41/3.00      | k2_struct_0(sK7) != k1_xboole_0 ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_8593]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_6654,plain,
% 19.41/3.00      ( ~ v1_xboole_0(X0)
% 19.41/3.00      | v1_xboole_0(u1_struct_0(X1))
% 19.41/3.00      | u1_struct_0(X1) != X0 ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_404]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_6726,plain,
% 19.41/3.00      ( v1_xboole_0(u1_struct_0(X0))
% 19.41/3.00      | ~ v1_xboole_0(k2_struct_0(X0))
% 19.41/3.00      | u1_struct_0(X0) != k2_struct_0(X0) ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_6654]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_6728,plain,
% 19.41/3.00      ( v1_xboole_0(u1_struct_0(sK7))
% 19.41/3.00      | ~ v1_xboole_0(k2_struct_0(sK7))
% 19.41/3.00      | u1_struct_0(sK7) != k2_struct_0(sK7) ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_6726]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_8,plain,
% 19.41/3.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 19.41/3.00      inference(cnf_transformation,[],[f64]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_4,plain,
% 19.41/3.00      ( r1_tarski(k1_xboole_0,X0) ),
% 19.41/3.00      inference(cnf_transformation,[],[f59]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_2875,plain,
% 19.41/3.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 19.41/3.00      inference(resolution,[status(thm)],[c_8,c_4]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_1,plain,
% 19.41/3.00      ( r2_hidden(sK2(X0),X0) | v1_xboole_0(X0) ),
% 19.41/3.00      inference(cnf_transformation,[],[f56]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_3085,plain,
% 19.41/3.00      ( v1_xboole_0(k1_xboole_0) ),
% 19.41/3.00      inference(resolution,[status(thm)],[c_2875,c_1]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_25,plain,
% 19.41/3.00      ( v2_struct_0(X0)
% 19.41/3.00      | ~ l1_struct_0(X0)
% 19.41/3.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 19.41/3.00      inference(cnf_transformation,[],[f81]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_53,plain,
% 19.41/3.00      ( v2_struct_0(sK7)
% 19.41/3.00      | ~ l1_struct_0(sK7)
% 19.41/3.00      | ~ v1_xboole_0(u1_struct_0(sK7)) ),
% 19.41/3.00      inference(instantiation,[status(thm)],[c_25]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(c_34,negated_conjecture,
% 19.41/3.00      ( ~ v2_struct_0(sK7) ),
% 19.41/3.00      inference(cnf_transformation,[],[f87]) ).
% 19.41/3.00  
% 19.41/3.00  cnf(contradiction,plain,
% 19.41/3.00      ( $false ),
% 19.41/3.00      inference(minisat,
% 19.41/3.00                [status(thm)],
% 19.41/3.00                [c_57276,c_8595,c_6728,c_3715,c_3713,c_3085,c_99,c_57,
% 19.41/3.00                 c_53,c_34,c_35]) ).
% 19.41/3.00  
% 19.41/3.00  
% 19.41/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.41/3.00  
% 19.41/3.00  ------                               Statistics
% 19.41/3.00  
% 19.41/3.00  ------ Selected
% 19.41/3.00  
% 19.41/3.00  total_time:                             2.438
% 19.41/3.00  
%------------------------------------------------------------------------------
