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
% DateTime   : Thu Dec  3 12:21:58 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 495 expanded)
%              Number of clauses        :   73 ( 140 expanded)
%              Number of leaves         :   20 ( 139 expanded)
%              Depth                    :   20
%              Number of atoms          :  599 (3582 expanded)
%              Number of equality atoms :   90 ( 126 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
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
    inference(pure_predicate_removal,[],[f10])).

fof(f12,plain,(
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
    inference(pure_predicate_removal,[],[f11])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( r1_tsep_1(X3,X2)
            | r1_tsep_1(X2,X3) )
          & ( ~ r1_tsep_1(X3,X1)
            | ~ r1_tsep_1(X1,X3) )
          & m1_pre_topc(X1,X2)
          & m1_pre_topc(X3,X0) )
     => ( ( r1_tsep_1(sK8,X2)
          | r1_tsep_1(X2,sK8) )
        & ( ~ r1_tsep_1(sK8,X1)
          | ~ r1_tsep_1(X1,sK8) )
        & m1_pre_topc(X1,X2)
        & m1_pre_topc(sK8,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
            ( ( r1_tsep_1(X3,sK7)
              | r1_tsep_1(sK7,X3) )
            & ( ~ r1_tsep_1(X3,X1)
              | ~ r1_tsep_1(X1,X3) )
            & m1_pre_topc(X1,sK7)
            & m1_pre_topc(X3,X0) )
        & m1_pre_topc(sK7,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
                & ( ~ r1_tsep_1(X3,sK6)
                  | ~ r1_tsep_1(sK6,X3) )
                & m1_pre_topc(sK6,X2)
                & m1_pre_topc(X3,X0) )
            & m1_pre_topc(X2,X0) )
        & m1_pre_topc(sK6,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
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
                  & m1_pre_topc(X3,sK5) )
              & m1_pre_topc(X2,sK5) )
          & m1_pre_topc(X1,sK5) )
      & l1_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( r1_tsep_1(sK8,sK7)
      | r1_tsep_1(sK7,sK8) )
    & ( ~ r1_tsep_1(sK8,sK6)
      | ~ r1_tsep_1(sK6,sK8) )
    & m1_pre_topc(sK6,sK7)
    & m1_pre_topc(sK8,sK5)
    & m1_pre_topc(sK7,sK5)
    & m1_pre_topc(sK6,sK5)
    & l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f23,f41,f40,f39,f38])).

fof(f68,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    m1_pre_topc(sK6,sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,
    ( r1_tsep_1(sK8,sK7)
    | r1_tsep_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f24,plain,(
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

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f35,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
              ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X1))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) )
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1)
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) )
          & ( ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1)
              & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
              & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) )
          & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
                    & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
                    & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f35,f34,f33])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f16,f25,f24])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,(
    m1_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,
    ( ~ r1_tsep_1(sK8,sK6)
    | ~ r1_tsep_1(sK6,sK8) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X3,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3514,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK7))
    | ~ r1_tarski(X1,u1_struct_0(sK7))
    | ~ r1_tarski(X0,u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5784,plain,
    ( r1_xboole_0(X0,k2_struct_0(sK6))
    | ~ r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK7))
    | ~ r1_tarski(X0,u1_struct_0(sK8))
    | ~ r1_tarski(k2_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_3514])).

cnf(c_6281,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK7))
    | r1_xboole_0(u1_struct_0(sK8),k2_struct_0(sK6))
    | ~ r1_tarski(u1_struct_0(sK8),u1_struct_0(sK8))
    | ~ r1_tarski(k2_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5784])).

cnf(c_3422,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))
    | ~ r1_tarski(X0,u1_struct_0(sK7))
    | ~ r1_tarski(X1,u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5760,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))
    | r1_xboole_0(k2_struct_0(sK6),X0)
    | ~ r1_tarski(X0,u1_struct_0(sK8))
    | ~ r1_tarski(k2_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_3422])).

cnf(c_6223,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))
    | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(sK8))
    | ~ r1_tarski(u1_struct_0(sK8),u1_struct_0(sK8))
    | ~ r1_tarski(k2_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5760])).

cnf(c_2559,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5031,plain,
    ( k2_struct_0(sK6) = k2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2559])).

cnf(c_2561,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3570,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,u1_struct_0(sK7))
    | X2 != X0
    | u1_struct_0(sK7) != X1 ),
    inference(instantiation,[status(thm)],[c_2561])).

cnf(c_3763,plain,
    ( r1_tarski(X0,u1_struct_0(sK7))
    | ~ r1_tarski(X1,k2_struct_0(sK7))
    | X0 != X1
    | u1_struct_0(sK7) != k2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3570])).

cnf(c_4153,plain,
    ( r1_tarski(X0,u1_struct_0(sK7))
    | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(sK7))
    | X0 != k2_struct_0(X1)
    | u1_struct_0(sK7) != k2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3763])).

cnf(c_4595,plain,
    ( r1_tarski(X0,u1_struct_0(sK7))
    | ~ r1_tarski(k2_struct_0(sK6),k2_struct_0(sK7))
    | X0 != k2_struct_0(sK6)
    | u1_struct_0(sK7) != k2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_4153])).

cnf(c_5030,plain,
    ( r1_tarski(k2_struct_0(sK6),u1_struct_0(sK7))
    | ~ r1_tarski(k2_struct_0(sK6),k2_struct_0(sK7))
    | u1_struct_0(sK7) != k2_struct_0(sK7)
    | k2_struct_0(sK6) != k2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4595])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4129,plain,
    ( r1_tarski(u1_struct_0(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_18,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_420,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK5 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_421,plain,
    ( ~ l1_pre_topc(sK5)
    | l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_423,plain,
    ( l1_pre_topc(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_421,c_29])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK6,sK7) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_377,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK6 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_378,plain,
    ( l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_431,plain,
    ( l1_pre_topc(sK6) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_423,c_378])).

cnf(c_483,plain,
    ( l1_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_431])).

cnf(c_484,plain,
    ( l1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_3058,plain,
    ( l1_struct_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_484])).

cnf(c_4,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3081,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3462,plain,
    ( u1_struct_0(sK6) = k2_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_3058,c_3081])).

cnf(c_20,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3070,plain,
    ( r1_tsep_1(X0,X1) = iProver_top
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3999,plain,
    ( r1_tsep_1(X0,sK6) = iProver_top
    | r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK6)) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3462,c_3070])).

cnf(c_4081,plain,
    ( r1_tsep_1(X0,sK6)
    | ~ r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK6))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3999])).

cnf(c_4083,plain,
    ( r1_tsep_1(sK8,sK6)
    | ~ r1_xboole_0(u1_struct_0(sK8),k2_struct_0(sK6))
    | ~ l1_struct_0(sK6)
    | ~ l1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_4081])).

cnf(c_3995,plain,
    ( r1_tsep_1(sK6,X0) = iProver_top
    | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3462,c_3070])).

cnf(c_4069,plain,
    ( r1_tsep_1(sK6,X0)
    | ~ r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3995])).

cnf(c_4071,plain,
    ( r1_tsep_1(sK6,sK8)
    | ~ r1_xboole_0(k2_struct_0(sK6),u1_struct_0(sK8))
    | ~ l1_struct_0(sK6)
    | ~ l1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_4069])).

cnf(c_23,negated_conjecture,
    ( r1_tsep_1(sK7,sK8)
    | r1_tsep_1(sK8,sK7) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3067,plain,
    ( r1_tsep_1(sK7,sK8) = iProver_top
    | r1_tsep_1(sK8,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3068,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_tsep_1(X1,X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3729,plain,
    ( r1_tsep_1(sK8,sK7) = iProver_top
    | l1_struct_0(sK7) != iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3067,c_3068])).

cnf(c_3730,plain,
    ( r1_tsep_1(sK8,sK7)
    | ~ l1_struct_0(sK7)
    | ~ l1_struct_0(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3729])).

cnf(c_476,plain,
    ( l1_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_423])).

cnf(c_477,plain,
    ( l1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_3059,plain,
    ( l1_struct_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_3461,plain,
    ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
    inference(superposition,[status(thm)],[c_3059,c_3081])).

cnf(c_3439,plain,
    ( r1_tsep_1(sK7,sK8)
    | ~ r1_tsep_1(sK8,sK7)
    | ~ l1_struct_0(sK7)
    | ~ l1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_21,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3440,plain,
    ( ~ r1_tsep_1(sK8,sK7)
    | r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK7))
    | ~ l1_struct_0(sK7)
    | ~ l1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3300,plain,
    ( ~ r1_tsep_1(sK7,sK8)
    | r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))
    | ~ l1_struct_0(sK7)
    | ~ l1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_6,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_321,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_17,c_6])).

cnf(c_325,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X0,X1)
    | sP0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_321,c_19])).

cnf(c_326,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_325])).

cnf(c_367,plain,
    ( sP0(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK6 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_326,c_25])).

cnf(c_368,plain,
    ( sP0(sK6,sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_430,plain,
    ( sP0(sK6,sK7) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_423,c_368])).

cnf(c_920,plain,
    ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
    | sK6 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_430])).

cnf(c_921,plain,
    ( r1_tarski(k2_struct_0(sK6),k2_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_920])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_398,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK5 != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_399,plain,
    ( ~ l1_pre_topc(sK5)
    | l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_46,plain,
    ( ~ l1_pre_topc(sK8)
    | l1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tsep_1(sK6,sK8)
    | ~ r1_tsep_1(sK8,sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6281,c_6223,c_5031,c_5030,c_4129,c_4083,c_4071,c_3730,c_3461,c_3439,c_3440,c_3300,c_921,c_484,c_477,c_399,c_46,c_24,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:27:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.67/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/0.98  
% 2.67/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.67/0.98  
% 2.67/0.98  ------  iProver source info
% 2.67/0.98  
% 2.67/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.67/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.67/0.98  git: non_committed_changes: false
% 2.67/0.98  git: last_make_outside_of_git: false
% 2.67/0.98  
% 2.67/0.98  ------ 
% 2.67/0.98  
% 2.67/0.98  ------ Input Options
% 2.67/0.98  
% 2.67/0.98  --out_options                           all
% 2.67/0.98  --tptp_safe_out                         true
% 2.67/0.98  --problem_path                          ""
% 2.67/0.98  --include_path                          ""
% 2.67/0.98  --clausifier                            res/vclausify_rel
% 2.67/0.98  --clausifier_options                    --mode clausify
% 2.67/0.98  --stdin                                 false
% 2.67/0.98  --stats_out                             all
% 2.67/0.98  
% 2.67/0.98  ------ General Options
% 2.67/0.98  
% 2.67/0.98  --fof                                   false
% 2.67/0.98  --time_out_real                         305.
% 2.67/0.98  --time_out_virtual                      -1.
% 2.67/0.98  --symbol_type_check                     false
% 2.67/0.98  --clausify_out                          false
% 2.67/0.98  --sig_cnt_out                           false
% 2.67/0.98  --trig_cnt_out                          false
% 2.67/0.98  --trig_cnt_out_tolerance                1.
% 2.67/0.98  --trig_cnt_out_sk_spl                   false
% 2.67/0.98  --abstr_cl_out                          false
% 2.67/0.98  
% 2.67/0.98  ------ Global Options
% 2.67/0.98  
% 2.67/0.98  --schedule                              default
% 2.67/0.98  --add_important_lit                     false
% 2.67/0.98  --prop_solver_per_cl                    1000
% 2.67/0.98  --min_unsat_core                        false
% 2.67/0.98  --soft_assumptions                      false
% 2.67/0.98  --soft_lemma_size                       3
% 2.67/0.98  --prop_impl_unit_size                   0
% 2.67/0.98  --prop_impl_unit                        []
% 2.67/0.98  --share_sel_clauses                     true
% 2.67/0.98  --reset_solvers                         false
% 2.67/0.98  --bc_imp_inh                            [conj_cone]
% 2.67/0.98  --conj_cone_tolerance                   3.
% 2.67/0.98  --extra_neg_conj                        none
% 2.67/0.98  --large_theory_mode                     true
% 2.67/0.98  --prolific_symb_bound                   200
% 2.67/0.98  --lt_threshold                          2000
% 2.67/0.98  --clause_weak_htbl                      true
% 2.67/0.98  --gc_record_bc_elim                     false
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing Options
% 2.67/0.98  
% 2.67/0.98  --preprocessing_flag                    true
% 2.67/0.98  --time_out_prep_mult                    0.1
% 2.67/0.98  --splitting_mode                        input
% 2.67/0.98  --splitting_grd                         true
% 2.67/0.98  --splitting_cvd                         false
% 2.67/0.98  --splitting_cvd_svl                     false
% 2.67/0.98  --splitting_nvd                         32
% 2.67/0.98  --sub_typing                            true
% 2.67/0.98  --prep_gs_sim                           true
% 2.67/0.98  --prep_unflatten                        true
% 2.67/0.98  --prep_res_sim                          true
% 2.67/0.98  --prep_upred                            true
% 2.67/0.98  --prep_sem_filter                       exhaustive
% 2.67/0.98  --prep_sem_filter_out                   false
% 2.67/0.98  --pred_elim                             true
% 2.67/0.98  --res_sim_input                         true
% 2.67/0.98  --eq_ax_congr_red                       true
% 2.67/0.98  --pure_diseq_elim                       true
% 2.67/0.98  --brand_transform                       false
% 2.67/0.98  --non_eq_to_eq                          false
% 2.67/0.98  --prep_def_merge                        true
% 2.67/0.98  --prep_def_merge_prop_impl              false
% 2.67/0.98  --prep_def_merge_mbd                    true
% 2.67/0.98  --prep_def_merge_tr_red                 false
% 2.67/0.98  --prep_def_merge_tr_cl                  false
% 2.67/0.98  --smt_preprocessing                     true
% 2.67/0.98  --smt_ac_axioms                         fast
% 2.67/0.98  --preprocessed_out                      false
% 2.67/0.98  --preprocessed_stats                    false
% 2.67/0.98  
% 2.67/0.98  ------ Abstraction refinement Options
% 2.67/0.98  
% 2.67/0.98  --abstr_ref                             []
% 2.67/0.98  --abstr_ref_prep                        false
% 2.67/0.98  --abstr_ref_until_sat                   false
% 2.67/0.98  --abstr_ref_sig_restrict                funpre
% 2.67/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/0.98  --abstr_ref_under                       []
% 2.67/0.98  
% 2.67/0.98  ------ SAT Options
% 2.67/0.98  
% 2.67/0.98  --sat_mode                              false
% 2.67/0.98  --sat_fm_restart_options                ""
% 2.67/0.98  --sat_gr_def                            false
% 2.67/0.98  --sat_epr_types                         true
% 2.67/0.98  --sat_non_cyclic_types                  false
% 2.67/0.98  --sat_finite_models                     false
% 2.67/0.98  --sat_fm_lemmas                         false
% 2.67/0.98  --sat_fm_prep                           false
% 2.67/0.98  --sat_fm_uc_incr                        true
% 2.67/0.98  --sat_out_model                         small
% 2.67/0.98  --sat_out_clauses                       false
% 2.67/0.98  
% 2.67/0.98  ------ QBF Options
% 2.67/0.98  
% 2.67/0.98  --qbf_mode                              false
% 2.67/0.98  --qbf_elim_univ                         false
% 2.67/0.98  --qbf_dom_inst                          none
% 2.67/0.98  --qbf_dom_pre_inst                      false
% 2.67/0.98  --qbf_sk_in                             false
% 2.67/0.98  --qbf_pred_elim                         true
% 2.67/0.98  --qbf_split                             512
% 2.67/0.98  
% 2.67/0.98  ------ BMC1 Options
% 2.67/0.98  
% 2.67/0.98  --bmc1_incremental                      false
% 2.67/0.98  --bmc1_axioms                           reachable_all
% 2.67/0.98  --bmc1_min_bound                        0
% 2.67/0.98  --bmc1_max_bound                        -1
% 2.67/0.98  --bmc1_max_bound_default                -1
% 2.67/0.98  --bmc1_symbol_reachability              true
% 2.67/0.98  --bmc1_property_lemmas                  false
% 2.67/0.98  --bmc1_k_induction                      false
% 2.67/0.98  --bmc1_non_equiv_states                 false
% 2.67/0.98  --bmc1_deadlock                         false
% 2.67/0.98  --bmc1_ucm                              false
% 2.67/0.98  --bmc1_add_unsat_core                   none
% 2.67/0.98  --bmc1_unsat_core_children              false
% 2.67/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/0.98  --bmc1_out_stat                         full
% 2.67/0.98  --bmc1_ground_init                      false
% 2.67/0.98  --bmc1_pre_inst_next_state              false
% 2.67/0.98  --bmc1_pre_inst_state                   false
% 2.67/0.98  --bmc1_pre_inst_reach_state             false
% 2.67/0.98  --bmc1_out_unsat_core                   false
% 2.67/0.98  --bmc1_aig_witness_out                  false
% 2.67/0.98  --bmc1_verbose                          false
% 2.67/0.98  --bmc1_dump_clauses_tptp                false
% 2.67/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.67/0.98  --bmc1_dump_file                        -
% 2.67/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.67/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.67/0.98  --bmc1_ucm_extend_mode                  1
% 2.67/0.98  --bmc1_ucm_init_mode                    2
% 2.67/0.98  --bmc1_ucm_cone_mode                    none
% 2.67/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.67/0.98  --bmc1_ucm_relax_model                  4
% 2.67/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.67/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/0.98  --bmc1_ucm_layered_model                none
% 2.67/0.98  --bmc1_ucm_max_lemma_size               10
% 2.67/0.98  
% 2.67/0.98  ------ AIG Options
% 2.67/0.98  
% 2.67/0.98  --aig_mode                              false
% 2.67/0.98  
% 2.67/0.98  ------ Instantiation Options
% 2.67/0.98  
% 2.67/0.98  --instantiation_flag                    true
% 2.67/0.98  --inst_sos_flag                         false
% 2.67/0.98  --inst_sos_phase                        true
% 2.67/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/0.98  --inst_lit_sel_side                     num_symb
% 2.67/0.98  --inst_solver_per_active                1400
% 2.67/0.98  --inst_solver_calls_frac                1.
% 2.67/0.98  --inst_passive_queue_type               priority_queues
% 2.67/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/0.98  --inst_passive_queues_freq              [25;2]
% 2.67/0.98  --inst_dismatching                      true
% 2.67/0.98  --inst_eager_unprocessed_to_passive     true
% 2.67/0.98  --inst_prop_sim_given                   true
% 2.67/0.98  --inst_prop_sim_new                     false
% 2.67/0.98  --inst_subs_new                         false
% 2.67/0.98  --inst_eq_res_simp                      false
% 2.67/0.98  --inst_subs_given                       false
% 2.67/0.98  --inst_orphan_elimination               true
% 2.67/0.98  --inst_learning_loop_flag               true
% 2.67/0.98  --inst_learning_start                   3000
% 2.67/0.98  --inst_learning_factor                  2
% 2.67/0.98  --inst_start_prop_sim_after_learn       3
% 2.67/0.98  --inst_sel_renew                        solver
% 2.67/0.98  --inst_lit_activity_flag                true
% 2.67/0.98  --inst_restr_to_given                   false
% 2.67/0.98  --inst_activity_threshold               500
% 2.67/0.98  --inst_out_proof                        true
% 2.67/0.98  
% 2.67/0.98  ------ Resolution Options
% 2.67/0.98  
% 2.67/0.98  --resolution_flag                       true
% 2.67/0.98  --res_lit_sel                           adaptive
% 2.67/0.98  --res_lit_sel_side                      none
% 2.67/0.98  --res_ordering                          kbo
% 2.67/0.98  --res_to_prop_solver                    active
% 2.67/0.98  --res_prop_simpl_new                    false
% 2.67/0.98  --res_prop_simpl_given                  true
% 2.67/0.98  --res_passive_queue_type                priority_queues
% 2.67/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/0.98  --res_passive_queues_freq               [15;5]
% 2.67/0.98  --res_forward_subs                      full
% 2.67/0.98  --res_backward_subs                     full
% 2.67/0.98  --res_forward_subs_resolution           true
% 2.67/0.98  --res_backward_subs_resolution          true
% 2.67/0.98  --res_orphan_elimination                true
% 2.67/0.98  --res_time_limit                        2.
% 2.67/0.98  --res_out_proof                         true
% 2.67/0.98  
% 2.67/0.98  ------ Superposition Options
% 2.67/0.98  
% 2.67/0.98  --superposition_flag                    true
% 2.67/0.98  --sup_passive_queue_type                priority_queues
% 2.67/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.67/0.98  --demod_completeness_check              fast
% 2.67/0.98  --demod_use_ground                      true
% 2.67/0.98  --sup_to_prop_solver                    passive
% 2.67/0.98  --sup_prop_simpl_new                    true
% 2.67/0.98  --sup_prop_simpl_given                  true
% 2.67/0.98  --sup_fun_splitting                     false
% 2.67/0.98  --sup_smt_interval                      50000
% 2.67/0.98  
% 2.67/0.98  ------ Superposition Simplification Setup
% 2.67/0.98  
% 2.67/0.98  --sup_indices_passive                   []
% 2.67/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.98  --sup_full_bw                           [BwDemod]
% 2.67/0.98  --sup_immed_triv                        [TrivRules]
% 2.67/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.98  --sup_immed_bw_main                     []
% 2.67/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.98  
% 2.67/0.98  ------ Combination Options
% 2.67/0.98  
% 2.67/0.98  --comb_res_mult                         3
% 2.67/0.98  --comb_sup_mult                         2
% 2.67/0.98  --comb_inst_mult                        10
% 2.67/0.98  
% 2.67/0.98  ------ Debug Options
% 2.67/0.98  
% 2.67/0.98  --dbg_backtrace                         false
% 2.67/0.98  --dbg_dump_prop_clauses                 false
% 2.67/0.98  --dbg_dump_prop_clauses_file            -
% 2.67/0.98  --dbg_out_stat                          false
% 2.67/0.98  ------ Parsing...
% 2.67/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.67/0.98  ------ Proving...
% 2.67/0.98  ------ Problem Properties 
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  clauses                                 27
% 2.67/0.98  conjectures                             2
% 2.67/0.98  EPR                                     14
% 2.67/0.98  Horn                                    22
% 2.67/0.98  unary                                   9
% 2.67/0.98  binary                                  4
% 2.67/0.98  lits                                    74
% 2.67/0.98  lits eq                                 5
% 2.67/0.98  fd_pure                                 0
% 2.67/0.98  fd_pseudo                               0
% 2.67/0.98  fd_cond                                 0
% 2.67/0.98  fd_pseudo_cond                          1
% 2.67/0.98  AC symbols                              0
% 2.67/0.98  
% 2.67/0.98  ------ Schedule dynamic 5 is on 
% 2.67/0.98  
% 2.67/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  ------ 
% 2.67/0.98  Current options:
% 2.67/0.98  ------ 
% 2.67/0.98  
% 2.67/0.98  ------ Input Options
% 2.67/0.98  
% 2.67/0.98  --out_options                           all
% 2.67/0.98  --tptp_safe_out                         true
% 2.67/0.98  --problem_path                          ""
% 2.67/0.98  --include_path                          ""
% 2.67/0.98  --clausifier                            res/vclausify_rel
% 2.67/0.98  --clausifier_options                    --mode clausify
% 2.67/0.98  --stdin                                 false
% 2.67/0.98  --stats_out                             all
% 2.67/0.98  
% 2.67/0.98  ------ General Options
% 2.67/0.98  
% 2.67/0.98  --fof                                   false
% 2.67/0.98  --time_out_real                         305.
% 2.67/0.98  --time_out_virtual                      -1.
% 2.67/0.98  --symbol_type_check                     false
% 2.67/0.98  --clausify_out                          false
% 2.67/0.98  --sig_cnt_out                           false
% 2.67/0.98  --trig_cnt_out                          false
% 2.67/0.98  --trig_cnt_out_tolerance                1.
% 2.67/0.98  --trig_cnt_out_sk_spl                   false
% 2.67/0.98  --abstr_cl_out                          false
% 2.67/0.98  
% 2.67/0.98  ------ Global Options
% 2.67/0.98  
% 2.67/0.98  --schedule                              default
% 2.67/0.98  --add_important_lit                     false
% 2.67/0.98  --prop_solver_per_cl                    1000
% 2.67/0.98  --min_unsat_core                        false
% 2.67/0.98  --soft_assumptions                      false
% 2.67/0.98  --soft_lemma_size                       3
% 2.67/0.98  --prop_impl_unit_size                   0
% 2.67/0.98  --prop_impl_unit                        []
% 2.67/0.98  --share_sel_clauses                     true
% 2.67/0.98  --reset_solvers                         false
% 2.67/0.98  --bc_imp_inh                            [conj_cone]
% 2.67/0.98  --conj_cone_tolerance                   3.
% 2.67/0.98  --extra_neg_conj                        none
% 2.67/0.98  --large_theory_mode                     true
% 2.67/0.98  --prolific_symb_bound                   200
% 2.67/0.98  --lt_threshold                          2000
% 2.67/0.98  --clause_weak_htbl                      true
% 2.67/0.98  --gc_record_bc_elim                     false
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing Options
% 2.67/0.98  
% 2.67/0.98  --preprocessing_flag                    true
% 2.67/0.98  --time_out_prep_mult                    0.1
% 2.67/0.98  --splitting_mode                        input
% 2.67/0.98  --splitting_grd                         true
% 2.67/0.98  --splitting_cvd                         false
% 2.67/0.98  --splitting_cvd_svl                     false
% 2.67/0.98  --splitting_nvd                         32
% 2.67/0.98  --sub_typing                            true
% 2.67/0.98  --prep_gs_sim                           true
% 2.67/0.98  --prep_unflatten                        true
% 2.67/0.98  --prep_res_sim                          true
% 2.67/0.98  --prep_upred                            true
% 2.67/0.98  --prep_sem_filter                       exhaustive
% 2.67/0.98  --prep_sem_filter_out                   false
% 2.67/0.98  --pred_elim                             true
% 2.67/0.98  --res_sim_input                         true
% 2.67/0.98  --eq_ax_congr_red                       true
% 2.67/0.98  --pure_diseq_elim                       true
% 2.67/0.98  --brand_transform                       false
% 2.67/0.98  --non_eq_to_eq                          false
% 2.67/0.98  --prep_def_merge                        true
% 2.67/0.98  --prep_def_merge_prop_impl              false
% 2.67/0.98  --prep_def_merge_mbd                    true
% 2.67/0.98  --prep_def_merge_tr_red                 false
% 2.67/0.98  --prep_def_merge_tr_cl                  false
% 2.67/0.98  --smt_preprocessing                     true
% 2.67/0.98  --smt_ac_axioms                         fast
% 2.67/0.98  --preprocessed_out                      false
% 2.67/0.98  --preprocessed_stats                    false
% 2.67/0.98  
% 2.67/0.98  ------ Abstraction refinement Options
% 2.67/0.98  
% 2.67/0.98  --abstr_ref                             []
% 2.67/0.98  --abstr_ref_prep                        false
% 2.67/0.98  --abstr_ref_until_sat                   false
% 2.67/0.98  --abstr_ref_sig_restrict                funpre
% 2.67/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/0.98  --abstr_ref_under                       []
% 2.67/0.98  
% 2.67/0.98  ------ SAT Options
% 2.67/0.98  
% 2.67/0.98  --sat_mode                              false
% 2.67/0.98  --sat_fm_restart_options                ""
% 2.67/0.98  --sat_gr_def                            false
% 2.67/0.98  --sat_epr_types                         true
% 2.67/0.98  --sat_non_cyclic_types                  false
% 2.67/0.98  --sat_finite_models                     false
% 2.67/0.98  --sat_fm_lemmas                         false
% 2.67/0.98  --sat_fm_prep                           false
% 2.67/0.98  --sat_fm_uc_incr                        true
% 2.67/0.98  --sat_out_model                         small
% 2.67/0.98  --sat_out_clauses                       false
% 2.67/0.98  
% 2.67/0.98  ------ QBF Options
% 2.67/0.98  
% 2.67/0.98  --qbf_mode                              false
% 2.67/0.98  --qbf_elim_univ                         false
% 2.67/0.98  --qbf_dom_inst                          none
% 2.67/0.98  --qbf_dom_pre_inst                      false
% 2.67/0.98  --qbf_sk_in                             false
% 2.67/0.98  --qbf_pred_elim                         true
% 2.67/0.98  --qbf_split                             512
% 2.67/0.98  
% 2.67/0.98  ------ BMC1 Options
% 2.67/0.98  
% 2.67/0.98  --bmc1_incremental                      false
% 2.67/0.98  --bmc1_axioms                           reachable_all
% 2.67/0.98  --bmc1_min_bound                        0
% 2.67/0.98  --bmc1_max_bound                        -1
% 2.67/0.98  --bmc1_max_bound_default                -1
% 2.67/0.98  --bmc1_symbol_reachability              true
% 2.67/0.98  --bmc1_property_lemmas                  false
% 2.67/0.98  --bmc1_k_induction                      false
% 2.67/0.98  --bmc1_non_equiv_states                 false
% 2.67/0.98  --bmc1_deadlock                         false
% 2.67/0.98  --bmc1_ucm                              false
% 2.67/0.98  --bmc1_add_unsat_core                   none
% 2.67/0.98  --bmc1_unsat_core_children              false
% 2.67/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/0.98  --bmc1_out_stat                         full
% 2.67/0.98  --bmc1_ground_init                      false
% 2.67/0.98  --bmc1_pre_inst_next_state              false
% 2.67/0.98  --bmc1_pre_inst_state                   false
% 2.67/0.98  --bmc1_pre_inst_reach_state             false
% 2.67/0.98  --bmc1_out_unsat_core                   false
% 2.67/0.98  --bmc1_aig_witness_out                  false
% 2.67/0.98  --bmc1_verbose                          false
% 2.67/0.98  --bmc1_dump_clauses_tptp                false
% 2.67/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.67/0.98  --bmc1_dump_file                        -
% 2.67/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.67/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.67/0.98  --bmc1_ucm_extend_mode                  1
% 2.67/0.98  --bmc1_ucm_init_mode                    2
% 2.67/0.98  --bmc1_ucm_cone_mode                    none
% 2.67/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.67/0.98  --bmc1_ucm_relax_model                  4
% 2.67/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.67/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/0.98  --bmc1_ucm_layered_model                none
% 2.67/0.98  --bmc1_ucm_max_lemma_size               10
% 2.67/0.98  
% 2.67/0.98  ------ AIG Options
% 2.67/0.98  
% 2.67/0.98  --aig_mode                              false
% 2.67/0.98  
% 2.67/0.98  ------ Instantiation Options
% 2.67/0.98  
% 2.67/0.98  --instantiation_flag                    true
% 2.67/0.98  --inst_sos_flag                         false
% 2.67/0.98  --inst_sos_phase                        true
% 2.67/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/0.98  --inst_lit_sel_side                     none
% 2.67/0.98  --inst_solver_per_active                1400
% 2.67/0.98  --inst_solver_calls_frac                1.
% 2.67/0.98  --inst_passive_queue_type               priority_queues
% 2.67/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/0.98  --inst_passive_queues_freq              [25;2]
% 2.67/0.98  --inst_dismatching                      true
% 2.67/0.98  --inst_eager_unprocessed_to_passive     true
% 2.67/0.98  --inst_prop_sim_given                   true
% 2.67/0.98  --inst_prop_sim_new                     false
% 2.67/0.98  --inst_subs_new                         false
% 2.67/0.98  --inst_eq_res_simp                      false
% 2.67/0.98  --inst_subs_given                       false
% 2.67/0.98  --inst_orphan_elimination               true
% 2.67/0.98  --inst_learning_loop_flag               true
% 2.67/0.98  --inst_learning_start                   3000
% 2.67/0.98  --inst_learning_factor                  2
% 2.67/0.98  --inst_start_prop_sim_after_learn       3
% 2.67/0.98  --inst_sel_renew                        solver
% 2.67/0.98  --inst_lit_activity_flag                true
% 2.67/0.98  --inst_restr_to_given                   false
% 2.67/0.98  --inst_activity_threshold               500
% 2.67/0.98  --inst_out_proof                        true
% 2.67/0.98  
% 2.67/0.98  ------ Resolution Options
% 2.67/0.98  
% 2.67/0.98  --resolution_flag                       false
% 2.67/0.98  --res_lit_sel                           adaptive
% 2.67/0.98  --res_lit_sel_side                      none
% 2.67/0.98  --res_ordering                          kbo
% 2.67/0.98  --res_to_prop_solver                    active
% 2.67/0.98  --res_prop_simpl_new                    false
% 2.67/0.98  --res_prop_simpl_given                  true
% 2.67/0.98  --res_passive_queue_type                priority_queues
% 2.67/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/0.98  --res_passive_queues_freq               [15;5]
% 2.67/0.98  --res_forward_subs                      full
% 2.67/0.98  --res_backward_subs                     full
% 2.67/0.98  --res_forward_subs_resolution           true
% 2.67/0.98  --res_backward_subs_resolution          true
% 2.67/0.98  --res_orphan_elimination                true
% 2.67/0.98  --res_time_limit                        2.
% 2.67/0.98  --res_out_proof                         true
% 2.67/0.98  
% 2.67/0.98  ------ Superposition Options
% 2.67/0.98  
% 2.67/0.98  --superposition_flag                    true
% 2.67/0.98  --sup_passive_queue_type                priority_queues
% 2.67/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.67/0.98  --demod_completeness_check              fast
% 2.67/0.98  --demod_use_ground                      true
% 2.67/0.98  --sup_to_prop_solver                    passive
% 2.67/0.98  --sup_prop_simpl_new                    true
% 2.67/0.98  --sup_prop_simpl_given                  true
% 2.67/0.98  --sup_fun_splitting                     false
% 2.67/0.98  --sup_smt_interval                      50000
% 2.67/0.98  
% 2.67/0.98  ------ Superposition Simplification Setup
% 2.67/0.98  
% 2.67/0.98  --sup_indices_passive                   []
% 2.67/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.98  --sup_full_bw                           [BwDemod]
% 2.67/0.98  --sup_immed_triv                        [TrivRules]
% 2.67/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.98  --sup_immed_bw_main                     []
% 2.67/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.98  
% 2.67/0.98  ------ Combination Options
% 2.67/0.98  
% 2.67/0.98  --comb_res_mult                         3
% 2.67/0.98  --comb_sup_mult                         2
% 2.67/0.98  --comb_inst_mult                        10
% 2.67/0.98  
% 2.67/0.98  ------ Debug Options
% 2.67/0.98  
% 2.67/0.98  --dbg_backtrace                         false
% 2.67/0.98  --dbg_dump_prop_clauses                 false
% 2.67/0.98  --dbg_dump_prop_clauses_file            -
% 2.67/0.98  --dbg_out_stat                          false
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  ------ Proving...
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  % SZS status Theorem for theBenchmark.p
% 2.67/0.98  
% 2.67/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.67/0.98  
% 2.67/0.98  fof(f2,axiom,(
% 2.67/0.98    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f13,plain,(
% 2.67/0.98    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 2.67/0.98    inference(ennf_transformation,[],[f2])).
% 2.67/0.98  
% 2.67/0.98  fof(f14,plain,(
% 2.67/0.98    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 2.67/0.98    inference(flattening,[],[f13])).
% 2.67/0.98  
% 2.67/0.98  fof(f46,plain,(
% 2.67/0.98    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f14])).
% 2.67/0.98  
% 2.67/0.98  fof(f1,axiom,(
% 2.67/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f27,plain,(
% 2.67/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.67/0.98    inference(nnf_transformation,[],[f1])).
% 2.67/0.98  
% 2.67/0.98  fof(f28,plain,(
% 2.67/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.67/0.98    inference(flattening,[],[f27])).
% 2.67/0.98  
% 2.67/0.98  fof(f43,plain,(
% 2.67/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.67/0.98    inference(cnf_transformation,[],[f28])).
% 2.67/0.98  
% 2.67/0.98  fof(f74,plain,(
% 2.67/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.67/0.98    inference(equality_resolution,[],[f43])).
% 2.67/0.98  
% 2.67/0.98  fof(f5,axiom,(
% 2.67/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f17,plain,(
% 2.67/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.67/0.98    inference(ennf_transformation,[],[f5])).
% 2.67/0.98  
% 2.67/0.98  fof(f61,plain,(
% 2.67/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f17])).
% 2.67/0.98  
% 2.67/0.98  fof(f6,axiom,(
% 2.67/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f18,plain,(
% 2.67/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.67/0.98    inference(ennf_transformation,[],[f6])).
% 2.67/0.98  
% 2.67/0.98  fof(f62,plain,(
% 2.67/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f18])).
% 2.67/0.98  
% 2.67/0.98  fof(f9,conjecture,(
% 2.67/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 2.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f10,negated_conjecture,(
% 2.67/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 2.67/0.98    inference(negated_conjecture,[],[f9])).
% 2.67/0.98  
% 2.67/0.98  fof(f11,plain,(
% 2.67/0.98    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 2.67/0.98    inference(pure_predicate_removal,[],[f10])).
% 2.67/0.98  
% 2.67/0.98  fof(f12,plain,(
% 2.67/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 2.67/0.98    inference(pure_predicate_removal,[],[f11])).
% 2.67/0.98  
% 2.67/0.98  fof(f22,plain,(
% 2.67/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 2.67/0.98    inference(ennf_transformation,[],[f12])).
% 2.67/0.98  
% 2.67/0.98  fof(f23,plain,(
% 2.67/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 2.67/0.98    inference(flattening,[],[f22])).
% 2.67/0.98  
% 2.67/0.98  fof(f41,plain,(
% 2.67/0.98    ( ! [X2,X0,X1] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) => ((r1_tsep_1(sK8,X2) | r1_tsep_1(X2,sK8)) & (~r1_tsep_1(sK8,X1) | ~r1_tsep_1(X1,sK8)) & m1_pre_topc(X1,X2) & m1_pre_topc(sK8,X0))) )),
% 2.67/0.98    introduced(choice_axiom,[])).
% 2.67/0.98  
% 2.67/0.98  fof(f40,plain,(
% 2.67/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) => (? [X3] : ((r1_tsep_1(X3,sK7) | r1_tsep_1(sK7,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,sK7) & m1_pre_topc(X3,X0)) & m1_pre_topc(sK7,X0))) )),
% 2.67/0.98    introduced(choice_axiom,[])).
% 2.67/0.98  
% 2.67/0.98  fof(f39,plain,(
% 2.67/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) => (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK6) | ~r1_tsep_1(sK6,X3)) & m1_pre_topc(sK6,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(sK6,X0))) )),
% 2.67/0.98    introduced(choice_axiom,[])).
% 2.67/0.98  
% 2.67/0.98  fof(f38,plain,(
% 2.67/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK5)) & m1_pre_topc(X2,sK5)) & m1_pre_topc(X1,sK5)) & l1_pre_topc(sK5))),
% 2.67/0.98    introduced(choice_axiom,[])).
% 2.67/0.98  
% 2.67/0.98  fof(f42,plain,(
% 2.67/0.98    ((((r1_tsep_1(sK8,sK7) | r1_tsep_1(sK7,sK8)) & (~r1_tsep_1(sK8,sK6) | ~r1_tsep_1(sK6,sK8)) & m1_pre_topc(sK6,sK7) & m1_pre_topc(sK8,sK5)) & m1_pre_topc(sK7,sK5)) & m1_pre_topc(sK6,sK5)) & l1_pre_topc(sK5)),
% 2.67/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f23,f41,f40,f39,f38])).
% 2.67/0.98  
% 2.67/0.98  fof(f68,plain,(
% 2.67/0.98    m1_pre_topc(sK7,sK5)),
% 2.67/0.98    inference(cnf_transformation,[],[f42])).
% 2.67/0.98  
% 2.67/0.98  fof(f66,plain,(
% 2.67/0.98    l1_pre_topc(sK5)),
% 2.67/0.98    inference(cnf_transformation,[],[f42])).
% 2.67/0.98  
% 2.67/0.98  fof(f70,plain,(
% 2.67/0.98    m1_pre_topc(sK6,sK7)),
% 2.67/0.98    inference(cnf_transformation,[],[f42])).
% 2.67/0.98  
% 2.67/0.98  fof(f3,axiom,(
% 2.67/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f15,plain,(
% 2.67/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.67/0.98    inference(ennf_transformation,[],[f3])).
% 2.67/0.98  
% 2.67/0.98  fof(f47,plain,(
% 2.67/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f15])).
% 2.67/0.98  
% 2.67/0.98  fof(f7,axiom,(
% 2.67/0.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 2.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f19,plain,(
% 2.67/0.98    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.67/0.98    inference(ennf_transformation,[],[f7])).
% 2.67/0.98  
% 2.67/0.98  fof(f37,plain,(
% 2.67/0.98    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.67/0.98    inference(nnf_transformation,[],[f19])).
% 2.67/0.98  
% 2.67/0.98  fof(f64,plain,(
% 2.67/0.98    ( ! [X0,X1] : (r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f37])).
% 2.67/0.98  
% 2.67/0.98  fof(f72,plain,(
% 2.67/0.98    r1_tsep_1(sK8,sK7) | r1_tsep_1(sK7,sK8)),
% 2.67/0.98    inference(cnf_transformation,[],[f42])).
% 2.67/0.98  
% 2.67/0.98  fof(f8,axiom,(
% 2.67/0.98    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 2.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f20,plain,(
% 2.67/0.98    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 2.67/0.98    inference(ennf_transformation,[],[f8])).
% 2.67/0.98  
% 2.67/0.98  fof(f21,plain,(
% 2.67/0.98    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 2.67/0.98    inference(flattening,[],[f20])).
% 2.67/0.98  
% 2.67/0.98  fof(f65,plain,(
% 2.67/0.98    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f21])).
% 2.67/0.98  
% 2.67/0.98  fof(f63,plain,(
% 2.67/0.98    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f37])).
% 2.67/0.98  
% 2.67/0.98  fof(f24,plain,(
% 2.67/0.98    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 2.67/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.67/0.98  
% 2.67/0.98  fof(f30,plain,(
% 2.67/0.98    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 2.67/0.98    inference(nnf_transformation,[],[f24])).
% 2.67/0.98  
% 2.67/0.98  fof(f31,plain,(
% 2.67/0.98    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 2.67/0.98    inference(flattening,[],[f30])).
% 2.67/0.98  
% 2.67/0.98  fof(f32,plain,(
% 2.67/0.98    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 2.67/0.98    inference(rectify,[],[f31])).
% 2.67/0.98  
% 2.67/0.98  fof(f35,plain,(
% 2.67/0.98    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 2.67/0.98    introduced(choice_axiom,[])).
% 2.67/0.98  
% 2.67/0.98  fof(f34,plain,(
% 2.67/0.98    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 2.67/0.98    introduced(choice_axiom,[])).
% 2.67/0.98  
% 2.67/0.98  fof(f33,plain,(
% 2.67/0.98    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.67/0.98    introduced(choice_axiom,[])).
% 2.67/0.98  
% 2.67/0.98  fof(f36,plain,(
% 2.67/0.98    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 2.67/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f35,f34,f33])).
% 2.67/0.98  
% 2.67/0.98  fof(f50,plain,(
% 2.67/0.98    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f36])).
% 2.67/0.98  
% 2.67/0.98  fof(f4,axiom,(
% 2.67/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 2.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f16,plain,(
% 2.67/0.98    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.67/0.98    inference(ennf_transformation,[],[f4])).
% 2.67/0.98  
% 2.67/0.98  fof(f25,plain,(
% 2.67/0.98    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 2.67/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.67/0.98  
% 2.67/0.98  fof(f26,plain,(
% 2.67/0.98    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.67/0.98    inference(definition_folding,[],[f16,f25,f24])).
% 2.67/0.98  
% 2.67/0.98  fof(f60,plain,(
% 2.67/0.98    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f26])).
% 2.67/0.98  
% 2.67/0.98  fof(f29,plain,(
% 2.67/0.98    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 2.67/0.98    inference(nnf_transformation,[],[f25])).
% 2.67/0.98  
% 2.67/0.98  fof(f48,plain,(
% 2.67/0.98    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f29])).
% 2.67/0.98  
% 2.67/0.98  fof(f69,plain,(
% 2.67/0.98    m1_pre_topc(sK8,sK5)),
% 2.67/0.98    inference(cnf_transformation,[],[f42])).
% 2.67/0.98  
% 2.67/0.98  fof(f71,plain,(
% 2.67/0.98    ~r1_tsep_1(sK8,sK6) | ~r1_tsep_1(sK6,sK8)),
% 2.67/0.98    inference(cnf_transformation,[],[f42])).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3,plain,
% 2.67/0.98      ( ~ r1_xboole_0(X0,X1)
% 2.67/0.98      | r1_xboole_0(X2,X3)
% 2.67/0.98      | ~ r1_tarski(X2,X0)
% 2.67/0.98      | ~ r1_tarski(X3,X1) ),
% 2.67/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3514,plain,
% 2.67/0.98      ( r1_xboole_0(X0,X1)
% 2.67/0.98      | ~ r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK7))
% 2.67/0.98      | ~ r1_tarski(X1,u1_struct_0(sK7))
% 2.67/0.98      | ~ r1_tarski(X0,u1_struct_0(sK8)) ),
% 2.67/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_5784,plain,
% 2.67/0.98      ( r1_xboole_0(X0,k2_struct_0(sK6))
% 2.67/0.98      | ~ r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK7))
% 2.67/0.98      | ~ r1_tarski(X0,u1_struct_0(sK8))
% 2.67/0.98      | ~ r1_tarski(k2_struct_0(sK6),u1_struct_0(sK7)) ),
% 2.67/0.98      inference(instantiation,[status(thm)],[c_3514]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_6281,plain,
% 2.67/0.98      ( ~ r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK7))
% 2.67/0.98      | r1_xboole_0(u1_struct_0(sK8),k2_struct_0(sK6))
% 2.67/0.98      | ~ r1_tarski(u1_struct_0(sK8),u1_struct_0(sK8))
% 2.67/0.98      | ~ r1_tarski(k2_struct_0(sK6),u1_struct_0(sK7)) ),
% 2.67/0.98      inference(instantiation,[status(thm)],[c_5784]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3422,plain,
% 2.67/0.98      ( r1_xboole_0(X0,X1)
% 2.67/0.98      | ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))
% 2.67/0.98      | ~ r1_tarski(X0,u1_struct_0(sK7))
% 2.67/0.98      | ~ r1_tarski(X1,u1_struct_0(sK8)) ),
% 2.67/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_5760,plain,
% 2.67/0.98      ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))
% 2.67/0.98      | r1_xboole_0(k2_struct_0(sK6),X0)
% 2.67/0.98      | ~ r1_tarski(X0,u1_struct_0(sK8))
% 2.67/0.98      | ~ r1_tarski(k2_struct_0(sK6),u1_struct_0(sK7)) ),
% 2.67/0.98      inference(instantiation,[status(thm)],[c_3422]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_6223,plain,
% 2.67/0.98      ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))
% 2.67/0.98      | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(sK8))
% 2.67/0.98      | ~ r1_tarski(u1_struct_0(sK8),u1_struct_0(sK8))
% 2.67/0.98      | ~ r1_tarski(k2_struct_0(sK6),u1_struct_0(sK7)) ),
% 2.67/0.98      inference(instantiation,[status(thm)],[c_5760]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_2559,plain,( X0 = X0 ),theory(equality) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_5031,plain,
% 2.67/0.98      ( k2_struct_0(sK6) = k2_struct_0(sK6) ),
% 2.67/0.98      inference(instantiation,[status(thm)],[c_2559]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_2561,plain,
% 2.67/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.67/0.98      theory(equality) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3570,plain,
% 2.67/0.98      ( ~ r1_tarski(X0,X1)
% 2.67/0.98      | r1_tarski(X2,u1_struct_0(sK7))
% 2.67/0.98      | X2 != X0
% 2.67/0.98      | u1_struct_0(sK7) != X1 ),
% 2.67/0.98      inference(instantiation,[status(thm)],[c_2561]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3763,plain,
% 2.67/0.98      ( r1_tarski(X0,u1_struct_0(sK7))
% 2.67/0.98      | ~ r1_tarski(X1,k2_struct_0(sK7))
% 2.67/0.98      | X0 != X1
% 2.67/0.98      | u1_struct_0(sK7) != k2_struct_0(sK7) ),
% 2.67/0.98      inference(instantiation,[status(thm)],[c_3570]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_4153,plain,
% 2.67/0.98      ( r1_tarski(X0,u1_struct_0(sK7))
% 2.67/0.98      | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(sK7))
% 2.67/0.98      | X0 != k2_struct_0(X1)
% 2.67/0.98      | u1_struct_0(sK7) != k2_struct_0(sK7) ),
% 2.67/0.98      inference(instantiation,[status(thm)],[c_3763]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_4595,plain,
% 2.67/0.98      ( r1_tarski(X0,u1_struct_0(sK7))
% 2.67/0.98      | ~ r1_tarski(k2_struct_0(sK6),k2_struct_0(sK7))
% 2.67/0.98      | X0 != k2_struct_0(sK6)
% 2.67/0.98      | u1_struct_0(sK7) != k2_struct_0(sK7) ),
% 2.67/0.98      inference(instantiation,[status(thm)],[c_4153]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_5030,plain,
% 2.67/0.98      ( r1_tarski(k2_struct_0(sK6),u1_struct_0(sK7))
% 2.67/0.98      | ~ r1_tarski(k2_struct_0(sK6),k2_struct_0(sK7))
% 2.67/0.98      | u1_struct_0(sK7) != k2_struct_0(sK7)
% 2.67/0.98      | k2_struct_0(sK6) != k2_struct_0(sK6) ),
% 2.67/0.98      inference(instantiation,[status(thm)],[c_4595]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_2,plain,
% 2.67/0.98      ( r1_tarski(X0,X0) ),
% 2.67/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_4129,plain,
% 2.67/0.98      ( r1_tarski(u1_struct_0(sK8),u1_struct_0(sK8)) ),
% 2.67/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_18,plain,
% 2.67/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.67/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_19,plain,
% 2.67/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.67/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_27,negated_conjecture,
% 2.67/0.98      ( m1_pre_topc(sK7,sK5) ),
% 2.67/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_420,plain,
% 2.67/0.98      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK5 != X0 | sK7 != X1 ),
% 2.67/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_421,plain,
% 2.67/0.98      ( ~ l1_pre_topc(sK5) | l1_pre_topc(sK7) ),
% 2.67/0.98      inference(unflattening,[status(thm)],[c_420]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_29,negated_conjecture,
% 2.67/0.98      ( l1_pre_topc(sK5) ),
% 2.67/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_423,plain,
% 2.67/0.98      ( l1_pre_topc(sK7) ),
% 2.67/0.98      inference(global_propositional_subsumption,
% 2.67/0.98                [status(thm)],
% 2.67/0.98                [c_421,c_29]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_25,negated_conjecture,
% 2.67/0.98      ( m1_pre_topc(sK6,sK7) ),
% 2.67/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_377,plain,
% 2.67/0.98      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK6 != X1 | sK7 != X0 ),
% 2.67/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_378,plain,
% 2.67/0.98      ( l1_pre_topc(sK6) | ~ l1_pre_topc(sK7) ),
% 2.67/0.98      inference(unflattening,[status(thm)],[c_377]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_431,plain,
% 2.67/0.98      ( l1_pre_topc(sK6) ),
% 2.67/0.98      inference(backward_subsumption_resolution,
% 2.67/0.98                [status(thm)],
% 2.67/0.98                [c_423,c_378]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_483,plain,
% 2.67/0.98      ( l1_struct_0(X0) | sK6 != X0 ),
% 2.67/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_431]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_484,plain,
% 2.67/0.98      ( l1_struct_0(sK6) ),
% 2.67/0.98      inference(unflattening,[status(thm)],[c_483]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3058,plain,
% 2.67/0.98      ( l1_struct_0(sK6) = iProver_top ),
% 2.67/0.98      inference(predicate_to_equality,[status(thm)],[c_484]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_4,plain,
% 2.67/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.67/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3081,plain,
% 2.67/0.98      ( u1_struct_0(X0) = k2_struct_0(X0)
% 2.67/0.98      | l1_struct_0(X0) != iProver_top ),
% 2.67/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3462,plain,
% 2.67/0.98      ( u1_struct_0(sK6) = k2_struct_0(sK6) ),
% 2.67/0.98      inference(superposition,[status(thm)],[c_3058,c_3081]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_20,plain,
% 2.67/0.98      ( r1_tsep_1(X0,X1)
% 2.67/0.98      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 2.67/0.98      | ~ l1_struct_0(X0)
% 2.67/0.98      | ~ l1_struct_0(X1) ),
% 2.67/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3070,plain,
% 2.67/0.98      ( r1_tsep_1(X0,X1) = iProver_top
% 2.67/0.98      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 2.67/0.98      | l1_struct_0(X0) != iProver_top
% 2.67/0.98      | l1_struct_0(X1) != iProver_top ),
% 2.67/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3999,plain,
% 2.67/0.98      ( r1_tsep_1(X0,sK6) = iProver_top
% 2.67/0.98      | r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK6)) != iProver_top
% 2.67/0.98      | l1_struct_0(X0) != iProver_top
% 2.67/0.98      | l1_struct_0(sK6) != iProver_top ),
% 2.67/0.98      inference(superposition,[status(thm)],[c_3462,c_3070]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_4081,plain,
% 2.67/0.98      ( r1_tsep_1(X0,sK6)
% 2.67/0.98      | ~ r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK6))
% 2.67/0.98      | ~ l1_struct_0(X0)
% 2.67/0.98      | ~ l1_struct_0(sK6) ),
% 2.67/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3999]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_4083,plain,
% 2.67/0.98      ( r1_tsep_1(sK8,sK6)
% 2.67/0.98      | ~ r1_xboole_0(u1_struct_0(sK8),k2_struct_0(sK6))
% 2.67/0.98      | ~ l1_struct_0(sK6)
% 2.67/0.98      | ~ l1_struct_0(sK8) ),
% 2.67/0.98      inference(instantiation,[status(thm)],[c_4081]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3995,plain,
% 2.67/0.98      ( r1_tsep_1(sK6,X0) = iProver_top
% 2.67/0.98      | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X0)) != iProver_top
% 2.67/0.98      | l1_struct_0(X0) != iProver_top
% 2.67/0.98      | l1_struct_0(sK6) != iProver_top ),
% 2.67/0.98      inference(superposition,[status(thm)],[c_3462,c_3070]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_4069,plain,
% 2.67/0.98      ( r1_tsep_1(sK6,X0)
% 2.67/0.98      | ~ r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X0))
% 2.67/0.98      | ~ l1_struct_0(X0)
% 2.67/0.98      | ~ l1_struct_0(sK6) ),
% 2.67/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3995]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_4071,plain,
% 2.67/0.98      ( r1_tsep_1(sK6,sK8)
% 2.67/0.98      | ~ r1_xboole_0(k2_struct_0(sK6),u1_struct_0(sK8))
% 2.67/0.98      | ~ l1_struct_0(sK6)
% 2.67/0.98      | ~ l1_struct_0(sK8) ),
% 2.67/0.98      inference(instantiation,[status(thm)],[c_4069]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_23,negated_conjecture,
% 2.67/0.98      ( r1_tsep_1(sK7,sK8) | r1_tsep_1(sK8,sK7) ),
% 2.67/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3067,plain,
% 2.67/0.98      ( r1_tsep_1(sK7,sK8) = iProver_top
% 2.67/0.98      | r1_tsep_1(sK8,sK7) = iProver_top ),
% 2.67/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_22,plain,
% 2.67/0.98      ( ~ r1_tsep_1(X0,X1)
% 2.67/0.98      | r1_tsep_1(X1,X0)
% 2.67/0.98      | ~ l1_struct_0(X0)
% 2.67/0.98      | ~ l1_struct_0(X1) ),
% 2.67/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3068,plain,
% 2.67/0.98      ( r1_tsep_1(X0,X1) != iProver_top
% 2.67/0.98      | r1_tsep_1(X1,X0) = iProver_top
% 2.67/0.98      | l1_struct_0(X0) != iProver_top
% 2.67/0.98      | l1_struct_0(X1) != iProver_top ),
% 2.67/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3729,plain,
% 2.67/0.98      ( r1_tsep_1(sK8,sK7) = iProver_top
% 2.67/0.98      | l1_struct_0(sK7) != iProver_top
% 2.67/0.98      | l1_struct_0(sK8) != iProver_top ),
% 2.67/0.98      inference(superposition,[status(thm)],[c_3067,c_3068]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3730,plain,
% 2.67/0.98      ( r1_tsep_1(sK8,sK7) | ~ l1_struct_0(sK7) | ~ l1_struct_0(sK8) ),
% 2.67/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3729]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_476,plain,
% 2.67/0.98      ( l1_struct_0(X0) | sK7 != X0 ),
% 2.67/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_423]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_477,plain,
% 2.67/0.98      ( l1_struct_0(sK7) ),
% 2.67/0.98      inference(unflattening,[status(thm)],[c_476]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3059,plain,
% 2.67/0.98      ( l1_struct_0(sK7) = iProver_top ),
% 2.67/0.98      inference(predicate_to_equality,[status(thm)],[c_477]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3461,plain,
% 2.67/0.98      ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
% 2.67/0.98      inference(superposition,[status(thm)],[c_3059,c_3081]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3439,plain,
% 2.67/0.98      ( r1_tsep_1(sK7,sK8)
% 2.67/0.98      | ~ r1_tsep_1(sK8,sK7)
% 2.67/0.98      | ~ l1_struct_0(sK7)
% 2.67/0.98      | ~ l1_struct_0(sK8) ),
% 2.67/0.98      inference(instantiation,[status(thm)],[c_22]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_21,plain,
% 2.67/0.98      ( ~ r1_tsep_1(X0,X1)
% 2.67/0.98      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 2.67/0.98      | ~ l1_struct_0(X0)
% 2.67/0.98      | ~ l1_struct_0(X1) ),
% 2.67/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3440,plain,
% 2.67/0.98      ( ~ r1_tsep_1(sK8,sK7)
% 2.67/0.98      | r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK7))
% 2.67/0.98      | ~ l1_struct_0(sK7)
% 2.67/0.98      | ~ l1_struct_0(sK8) ),
% 2.67/0.98      inference(instantiation,[status(thm)],[c_21]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3300,plain,
% 2.67/0.98      ( ~ r1_tsep_1(sK7,sK8)
% 2.67/0.98      | r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))
% 2.67/0.98      | ~ l1_struct_0(sK7)
% 2.67/0.98      | ~ l1_struct_0(sK8) ),
% 2.67/0.98      inference(instantiation,[status(thm)],[c_21]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_16,plain,
% 2.67/0.98      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 2.67/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_17,plain,
% 2.67/0.98      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 2.67/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_6,plain,
% 2.67/0.98      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 2.67/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_321,plain,
% 2.67/0.98      ( sP0(X0,X1)
% 2.67/0.98      | ~ m1_pre_topc(X0,X1)
% 2.67/0.98      | ~ l1_pre_topc(X1)
% 2.67/0.98      | ~ l1_pre_topc(X0) ),
% 2.67/0.98      inference(resolution,[status(thm)],[c_17,c_6]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_325,plain,
% 2.67/0.98      ( ~ l1_pre_topc(X1) | ~ m1_pre_topc(X0,X1) | sP0(X0,X1) ),
% 2.67/0.98      inference(global_propositional_subsumption,
% 2.67/0.98                [status(thm)],
% 2.67/0.98                [c_321,c_19]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_326,plain,
% 2.67/0.98      ( sP0(X0,X1) | ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) ),
% 2.67/0.98      inference(renaming,[status(thm)],[c_325]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_367,plain,
% 2.67/0.98      ( sP0(X0,X1) | ~ l1_pre_topc(X1) | sK6 != X0 | sK7 != X1 ),
% 2.67/0.98      inference(resolution_lifted,[status(thm)],[c_326,c_25]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_368,plain,
% 2.67/0.98      ( sP0(sK6,sK7) | ~ l1_pre_topc(sK7) ),
% 2.67/0.98      inference(unflattening,[status(thm)],[c_367]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_430,plain,
% 2.67/0.98      ( sP0(sK6,sK7) ),
% 2.67/0.98      inference(backward_subsumption_resolution,
% 2.67/0.98                [status(thm)],
% 2.67/0.98                [c_423,c_368]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_920,plain,
% 2.67/0.98      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
% 2.67/0.98      | sK6 != X0
% 2.67/0.98      | sK7 != X1 ),
% 2.67/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_430]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_921,plain,
% 2.67/0.98      ( r1_tarski(k2_struct_0(sK6),k2_struct_0(sK7)) ),
% 2.67/0.98      inference(unflattening,[status(thm)],[c_920]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_26,negated_conjecture,
% 2.67/0.98      ( m1_pre_topc(sK8,sK5) ),
% 2.67/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_398,plain,
% 2.67/0.98      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK5 != X0 | sK8 != X1 ),
% 2.67/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_399,plain,
% 2.67/0.98      ( ~ l1_pre_topc(sK5) | l1_pre_topc(sK8) ),
% 2.67/0.98      inference(unflattening,[status(thm)],[c_398]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_46,plain,
% 2.67/0.98      ( ~ l1_pre_topc(sK8) | l1_struct_0(sK8) ),
% 2.67/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_24,negated_conjecture,
% 2.67/0.98      ( ~ r1_tsep_1(sK6,sK8) | ~ r1_tsep_1(sK8,sK6) ),
% 2.67/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(contradiction,plain,
% 2.67/0.98      ( $false ),
% 2.67/0.98      inference(minisat,
% 2.67/0.98                [status(thm)],
% 2.67/0.98                [c_6281,c_6223,c_5031,c_5030,c_4129,c_4083,c_4071,c_3730,
% 2.67/0.98                 c_3461,c_3439,c_3440,c_3300,c_921,c_484,c_477,c_399,
% 2.67/0.98                 c_46,c_24,c_29]) ).
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.67/0.98  
% 2.67/0.98  ------                               Statistics
% 2.67/0.98  
% 2.67/0.98  ------ General
% 2.67/0.98  
% 2.67/0.98  abstr_ref_over_cycles:                  0
% 2.67/0.98  abstr_ref_under_cycles:                 0
% 2.67/0.98  gc_basic_clause_elim:                   0
% 2.67/0.98  forced_gc_time:                         0
% 2.67/0.98  parsing_time:                           0.01
% 2.67/0.98  unif_index_cands_time:                  0.
% 2.67/0.98  unif_index_add_time:                    0.
% 2.67/0.98  orderings_time:                         0.
% 2.67/0.98  out_proof_time:                         0.011
% 2.67/0.98  total_time:                             0.171
% 2.67/0.98  num_of_symbols:                         53
% 2.67/0.98  num_of_terms:                           2929
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing
% 2.67/0.98  
% 2.67/0.98  num_of_splits:                          0
% 2.67/0.98  num_of_split_atoms:                     0
% 2.67/0.98  num_of_reused_defs:                     0
% 2.67/0.98  num_eq_ax_congr_red:                    35
% 2.67/0.98  num_of_sem_filtered_clauses:            1
% 2.67/0.98  num_of_subtypes:                        0
% 2.67/0.98  monotx_restored_types:                  0
% 2.67/0.98  sat_num_of_epr_types:                   0
% 2.67/0.98  sat_num_of_non_cyclic_types:            0
% 2.67/0.98  sat_guarded_non_collapsed_types:        0
% 2.67/0.98  num_pure_diseq_elim:                    0
% 2.67/0.98  simp_replaced_by:                       0
% 2.67/0.98  res_preprocessed:                       133
% 2.67/0.98  prep_upred:                             0
% 2.67/0.98  prep_unflattend:                        180
% 2.67/0.98  smt_new_axioms:                         0
% 2.67/0.98  pred_elim_cands:                        7
% 2.67/0.98  pred_elim:                              3
% 2.67/0.98  pred_elim_cl:                           2
% 2.67/0.98  pred_elim_cycles:                       5
% 2.67/0.98  merged_defs:                            0
% 2.67/0.98  merged_defs_ncl:                        0
% 2.67/0.98  bin_hyper_res:                          0
% 2.67/0.98  prep_cycles:                            4
% 2.67/0.98  pred_elim_time:                         0.042
% 2.67/0.98  splitting_time:                         0.
% 2.67/0.98  sem_filter_time:                        0.
% 2.67/0.98  monotx_time:                            0.001
% 2.67/0.98  subtype_inf_time:                       0.
% 2.67/0.98  
% 2.67/0.98  ------ Problem properties
% 2.67/0.98  
% 2.67/0.98  clauses:                                27
% 2.67/0.98  conjectures:                            2
% 2.67/0.98  epr:                                    14
% 2.67/0.98  horn:                                   22
% 2.67/0.98  ground:                                 10
% 2.67/0.98  unary:                                  9
% 2.67/0.98  binary:                                 4
% 2.67/0.98  lits:                                   74
% 2.67/0.98  lits_eq:                                5
% 2.67/0.98  fd_pure:                                0
% 2.67/0.98  fd_pseudo:                              0
% 2.67/0.98  fd_cond:                                0
% 2.67/0.98  fd_pseudo_cond:                         1
% 2.67/0.98  ac_symbols:                             0
% 2.67/0.98  
% 2.67/0.98  ------ Propositional Solver
% 2.67/0.98  
% 2.67/0.98  prop_solver_calls:                      32
% 2.67/0.98  prop_fast_solver_calls:                 1364
% 2.67/0.98  smt_solver_calls:                       0
% 2.67/0.98  smt_fast_solver_calls:                  0
% 2.67/0.98  prop_num_of_clauses:                    1388
% 2.67/0.98  prop_preprocess_simplified:             5481
% 2.67/0.98  prop_fo_subsumed:                       21
% 2.67/0.98  prop_solver_time:                       0.
% 2.67/0.98  smt_solver_time:                        0.
% 2.67/0.98  smt_fast_solver_time:                   0.
% 2.67/0.98  prop_fast_solver_time:                  0.
% 2.67/0.98  prop_unsat_core_time:                   0.
% 2.67/0.98  
% 2.67/0.98  ------ QBF
% 2.67/0.98  
% 2.67/0.98  qbf_q_res:                              0
% 2.67/0.98  qbf_num_tautologies:                    0
% 2.67/0.98  qbf_prep_cycles:                        0
% 2.67/0.98  
% 2.67/0.98  ------ BMC1
% 2.67/0.98  
% 2.67/0.98  bmc1_current_bound:                     -1
% 2.67/0.98  bmc1_last_solved_bound:                 -1
% 2.67/0.98  bmc1_unsat_core_size:                   -1
% 2.67/0.98  bmc1_unsat_core_parents_size:           -1
% 2.67/0.98  bmc1_merge_next_fun:                    0
% 2.67/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.67/0.98  
% 2.67/0.98  ------ Instantiation
% 2.67/0.98  
% 2.67/0.98  inst_num_of_clauses:                    349
% 2.67/0.98  inst_num_in_passive:                    76
% 2.67/0.98  inst_num_in_active:                     266
% 2.67/0.98  inst_num_in_unprocessed:                6
% 2.67/0.98  inst_num_of_loops:                      292
% 2.67/0.98  inst_num_of_learning_restarts:          0
% 2.67/0.98  inst_num_moves_active_passive:          17
% 2.67/0.98  inst_lit_activity:                      0
% 2.67/0.98  inst_lit_activity_moves:                0
% 2.67/0.98  inst_num_tautologies:                   0
% 2.67/0.98  inst_num_prop_implied:                  0
% 2.67/0.98  inst_num_existing_simplified:           0
% 2.67/0.98  inst_num_eq_res_simplified:             0
% 2.67/0.98  inst_num_child_elim:                    0
% 2.67/0.98  inst_num_of_dismatching_blockings:      52
% 2.67/0.98  inst_num_of_non_proper_insts:           472
% 2.67/0.98  inst_num_of_duplicates:                 0
% 2.67/0.98  inst_inst_num_from_inst_to_res:         0
% 2.67/0.98  inst_dismatching_checking_time:         0.
% 2.67/0.98  
% 2.67/0.98  ------ Resolution
% 2.67/0.98  
% 2.67/0.98  res_num_of_clauses:                     0
% 2.67/0.98  res_num_in_passive:                     0
% 2.67/0.98  res_num_in_active:                      0
% 2.67/0.98  res_num_of_loops:                       137
% 2.67/0.98  res_forward_subset_subsumed:            87
% 2.67/0.98  res_backward_subset_subsumed:           0
% 2.67/0.98  res_forward_subsumed:                   0
% 2.67/0.98  res_backward_subsumed:                  0
% 2.67/0.98  res_forward_subsumption_resolution:     0
% 2.67/0.98  res_backward_subsumption_resolution:    2
% 2.67/0.98  res_clause_to_clause_subsumption:       242
% 2.67/0.98  res_orphan_elimination:                 0
% 2.67/0.98  res_tautology_del:                      78
% 2.67/0.98  res_num_eq_res_simplified:              0
% 2.67/0.98  res_num_sel_changes:                    0
% 2.67/0.98  res_moves_from_active_to_pass:          0
% 2.67/0.98  
% 2.67/0.98  ------ Superposition
% 2.67/0.98  
% 2.67/0.98  sup_time_total:                         0.
% 2.67/0.98  sup_time_generating:                    0.
% 2.67/0.98  sup_time_sim_full:                      0.
% 2.67/0.98  sup_time_sim_immed:                     0.
% 2.67/0.98  
% 2.67/0.98  sup_num_of_clauses:                     108
% 2.67/0.98  sup_num_in_active:                      57
% 2.67/0.98  sup_num_in_passive:                     51
% 2.67/0.98  sup_num_of_loops:                       58
% 2.67/0.98  sup_fw_superposition:                   84
% 2.67/0.98  sup_bw_superposition:                   10
% 2.67/0.98  sup_immediate_simplified:               8
% 2.67/0.98  sup_given_eliminated:                   0
% 2.67/0.98  comparisons_done:                       0
% 2.67/0.98  comparisons_avoided:                    0
% 2.67/0.98  
% 2.67/0.98  ------ Simplifications
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  sim_fw_subset_subsumed:                 0
% 2.67/0.98  sim_bw_subset_subsumed:                 1
% 2.67/0.98  sim_fw_subsumed:                        0
% 2.67/0.98  sim_bw_subsumed:                        0
% 2.67/0.98  sim_fw_subsumption_res:                 0
% 2.67/0.98  sim_bw_subsumption_res:                 0
% 2.67/0.98  sim_tautology_del:                      4
% 2.67/0.98  sim_eq_tautology_del:                   2
% 2.67/0.98  sim_eq_res_simp:                        0
% 2.67/0.98  sim_fw_demodulated:                     0
% 2.67/0.98  sim_bw_demodulated:                     0
% 2.67/0.98  sim_light_normalised:                   8
% 2.67/0.98  sim_joinable_taut:                      0
% 2.67/0.98  sim_joinable_simp:                      0
% 2.67/0.98  sim_ac_normalised:                      0
% 2.67/0.98  sim_smt_subsumption:                    0
% 2.67/0.98  
%------------------------------------------------------------------------------
