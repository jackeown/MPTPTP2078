%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:57 EST 2020

% Result     : Theorem 7.79s
% Output     : CNFRefutation 7.79s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 564 expanded)
%              Number of clauses        :   86 ( 176 expanded)
%              Number of leaves         :   20 ( 161 expanded)
%              Depth                    :   18
%              Number of atoms          :  635 (4735 expanded)
%              Number of equality atoms :  160 ( 237 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

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
    inference(pure_predicate_removal,[],[f14])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( r1_tsep_1(X3,X2)
            | r1_tsep_1(X2,X3) )
          & ( ~ r1_tsep_1(X3,X1)
            | ~ r1_tsep_1(X1,X3) )
          & m1_pre_topc(X1,X2)
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ( r1_tsep_1(sK8,X2)
          | r1_tsep_1(X2,sK8) )
        & ( ~ r1_tsep_1(sK8,X1)
          | ~ r1_tsep_1(X1,sK8) )
        & m1_pre_topc(X1,X2)
        & m1_pre_topc(sK8,X0)
        & ~ v2_struct_0(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & ( ~ r1_tsep_1(X3,X1)
                | ~ r1_tsep_1(X1,X3) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ( r1_tsep_1(X3,sK7)
              | r1_tsep_1(sK7,X3) )
            & ( ~ r1_tsep_1(X3,X1)
              | ~ r1_tsep_1(X1,X3) )
            & m1_pre_topc(X1,sK7)
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK7,X0)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & ( ~ r1_tsep_1(X3,sK6)
                  | ~ r1_tsep_1(sK6,X3) )
                & m1_pre_topc(sK6,X2)
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & m1_pre_topc(X1,X2)
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
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK5)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK5)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK5)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( r1_tsep_1(sK8,sK7)
      | r1_tsep_1(sK7,sK8) )
    & ( ~ r1_tsep_1(sK8,sK6)
      | ~ r1_tsep_1(sK6,sK8) )
    & m1_pre_topc(sK6,sK7)
    & m1_pre_topc(sK8,sK5)
    & ~ v2_struct_0(sK8)
    & m1_pre_topc(sK7,sK5)
    & ~ v2_struct_0(sK7)
    & m1_pre_topc(sK6,sK5)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f31,f50,f49,f48,f47])).

fof(f89,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f75,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f85,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f74,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f92,plain,(
    m1_pre_topc(sK6,sK7) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f32,plain,(
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

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f20,f33,f32])).

fof(f73,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

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
    inference(nnf_transformation,[],[f32])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f43,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f40,f43,f42,f41])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f87,plain,(
    m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f94,plain,
    ( r1_tsep_1(sK8,sK7)
    | r1_tsep_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,
    ( ~ r1_tsep_1(sK8,sK6)
    | ~ r1_tsep_1(sK6,sK8) ),
    inference(cnf_transformation,[],[f51])).

fof(f91,plain,(
    m1_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_37,negated_conjecture,
    ( m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3368,plain,
    ( m1_pre_topc(sK7,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3381,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4282,plain,
    ( l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3368,c_3381])).

cnf(c_41,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_44,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_48,plain,
    ( m1_pre_topc(sK7,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3623,plain,
    ( ~ m1_pre_topc(sK7,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_3719,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_3623])).

cnf(c_3720,plain,
    ( m1_pre_topc(sK7,sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3719])).

cnf(c_4586,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4282,c_44,c_48,c_3720])).

cnf(c_22,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3382,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4590,plain,
    ( l1_struct_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_4586,c_3382])).

cnf(c_8,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3393,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7087,plain,
    ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
    inference(superposition,[status(thm)],[c_4590,c_3393])).

cnf(c_27,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3378,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8322,plain,
    ( r1_tsep_1(X0,sK7) != iProver_top
    | r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK7)) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_7087,c_3378])).

cnf(c_27983,plain,
    ( l1_struct_0(X0) != iProver_top
    | r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK7)) = iProver_top
    | r1_tsep_1(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8322,c_4590])).

cnf(c_27984,plain,
    ( r1_tsep_1(X0,sK7) != iProver_top
    | r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK7)) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_27983])).

cnf(c_34,negated_conjecture,
    ( m1_pre_topc(sK6,sK7) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3371,plain,
    ( m1_pre_topc(sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_21,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_10,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_468,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_21,c_10])).

cnf(c_472,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X0,X1)
    | sP0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_468,c_23])).

cnf(c_473,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_472])).

cnf(c_3361,plain,
    ( sP0(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_4089,plain,
    ( sP0(sK6,sK7) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3371,c_3361])).

cnf(c_4598,plain,
    ( sP0(sK6,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4089,c_44,c_48,c_3720])).

cnf(c_20,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3383,plain,
    ( sP0(X0,X1) != iProver_top
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3394,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3395,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3400,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4290,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(k2_xboole_0(X0,X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3395,c_3400])).

cnf(c_9522,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3394,c_4290])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_135,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10966,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9522,c_135])).

cnf(c_10973,plain,
    ( k2_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X0)
    | sP0(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3383,c_10966])).

cnf(c_11601,plain,
    ( k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6)) = k2_struct_0(sK7) ),
    inference(superposition,[status(thm)],[c_4598,c_10973])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3398,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11702,plain,
    ( r1_xboole_0(X0,k2_struct_0(sK6)) = iProver_top
    | r1_xboole_0(X0,k2_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11601,c_3398])).

cnf(c_27996,plain,
    ( r1_tsep_1(X0,sK7) != iProver_top
    | r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK6)) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_27984,c_11702])).

cnf(c_28003,plain,
    ( r1_tsep_1(sK8,sK7) != iProver_top
    | r1_xboole_0(u1_struct_0(sK8),k2_struct_0(sK6)) = iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_27996])).

cnf(c_4280,plain,
    ( l1_pre_topc(sK6) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3371,c_3381])).

cnf(c_39,negated_conjecture,
    ( m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_46,plain,
    ( m1_pre_topc(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_3671,plain,
    ( ~ m1_pre_topc(X0,sK5)
    | l1_pre_topc(X0)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_3752,plain,
    ( ~ m1_pre_topc(sK6,sK5)
    | ~ l1_pre_topc(sK5)
    | l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_3671])).

cnf(c_3753,plain,
    ( m1_pre_topc(sK6,sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3752])).

cnf(c_4442,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4280,c_44,c_46,c_3753])).

cnf(c_4446,plain,
    ( l1_struct_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4442,c_3382])).

cnf(c_6163,plain,
    ( u1_struct_0(sK6) = k2_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_4446,c_3393])).

cnf(c_26,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3379,plain,
    ( r1_tsep_1(X0,X1) = iProver_top
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7853,plain,
    ( r1_tsep_1(X0,sK6) = iProver_top
    | r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK6)) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6163,c_3379])).

cnf(c_7880,plain,
    ( r1_tsep_1(sK8,sK6) = iProver_top
    | r1_xboole_0(u1_struct_0(sK8),k2_struct_0(sK6)) != iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7853])).

cnf(c_32,negated_conjecture,
    ( r1_tsep_1(sK7,sK8)
    | r1_tsep_1(sK8,sK7) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3373,plain,
    ( r1_tsep_1(sK7,sK8) = iProver_top
    | r1_tsep_1(sK8,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3374,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_tsep_1(X1,X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4929,plain,
    ( r1_tsep_1(sK8,sK7) = iProver_top
    | l1_struct_0(sK7) != iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3373,c_3374])).

cnf(c_33,negated_conjecture,
    ( ~ r1_tsep_1(sK6,sK8)
    | ~ r1_tsep_1(sK8,sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3372,plain,
    ( r1_tsep_1(sK6,sK8) != iProver_top
    | r1_tsep_1(sK8,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_35,negated_conjecture,
    ( m1_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_50,plain,
    ( m1_pre_topc(sK8,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_52,plain,
    ( r1_tsep_1(sK6,sK8) != iProver_top
    | r1_tsep_1(sK8,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_77,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_79,plain,
    ( l1_pre_topc(sK8) != iProver_top
    | l1_struct_0(sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_77])).

cnf(c_3456,plain,
    ( r1_tsep_1(sK6,sK8)
    | ~ r1_tsep_1(sK8,sK6)
    | ~ l1_struct_0(sK6)
    | ~ l1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_3457,plain,
    ( r1_tsep_1(sK6,sK8) = iProver_top
    | r1_tsep_1(sK8,sK6) != iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3456])).

cnf(c_3583,plain,
    ( ~ l1_pre_topc(sK6)
    | l1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3584,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_struct_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3583])).

cnf(c_3672,plain,
    ( m1_pre_topc(X0,sK5) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3671])).

cnf(c_3674,plain,
    ( m1_pre_topc(sK8,sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3672])).

cnf(c_3802,plain,
    ( r1_tsep_1(sK8,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3372,c_44,c_46,c_50,c_52,c_79,c_3457,c_3584,c_3674,c_3753])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28003,c_7880,c_4929,c_4590,c_3802,c_3753,c_3674,c_3584,c_79,c_50,c_46,c_44])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:11:14 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.18/0.34  % Running in FOF mode
% 7.79/1.43  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.79/1.43  
% 7.79/1.43  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.79/1.43  
% 7.79/1.43  ------  iProver source info
% 7.79/1.43  
% 7.79/1.43  git: date: 2020-06-30 10:37:57 +0100
% 7.79/1.43  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.79/1.43  git: non_committed_changes: false
% 7.79/1.43  git: last_make_outside_of_git: false
% 7.79/1.43  
% 7.79/1.43  ------ 
% 7.79/1.43  
% 7.79/1.43  ------ Input Options
% 7.79/1.43  
% 7.79/1.43  --out_options                           all
% 7.79/1.43  --tptp_safe_out                         true
% 7.79/1.43  --problem_path                          ""
% 7.79/1.43  --include_path                          ""
% 7.79/1.43  --clausifier                            res/vclausify_rel
% 7.79/1.43  --clausifier_options                    ""
% 7.79/1.43  --stdin                                 false
% 7.79/1.43  --stats_out                             all
% 7.79/1.43  
% 7.79/1.43  ------ General Options
% 7.79/1.43  
% 7.79/1.43  --fof                                   false
% 7.79/1.43  --time_out_real                         305.
% 7.79/1.43  --time_out_virtual                      -1.
% 7.79/1.43  --symbol_type_check                     false
% 7.79/1.43  --clausify_out                          false
% 7.79/1.43  --sig_cnt_out                           false
% 7.79/1.43  --trig_cnt_out                          false
% 7.79/1.43  --trig_cnt_out_tolerance                1.
% 7.79/1.43  --trig_cnt_out_sk_spl                   false
% 7.79/1.43  --abstr_cl_out                          false
% 7.79/1.43  
% 7.79/1.43  ------ Global Options
% 7.79/1.43  
% 7.79/1.43  --schedule                              default
% 7.79/1.43  --add_important_lit                     false
% 7.79/1.43  --prop_solver_per_cl                    1000
% 7.79/1.43  --min_unsat_core                        false
% 7.79/1.43  --soft_assumptions                      false
% 7.79/1.43  --soft_lemma_size                       3
% 7.79/1.43  --prop_impl_unit_size                   0
% 7.79/1.43  --prop_impl_unit                        []
% 7.79/1.43  --share_sel_clauses                     true
% 7.79/1.43  --reset_solvers                         false
% 7.79/1.43  --bc_imp_inh                            [conj_cone]
% 7.79/1.43  --conj_cone_tolerance                   3.
% 7.79/1.43  --extra_neg_conj                        none
% 7.79/1.43  --large_theory_mode                     true
% 7.79/1.43  --prolific_symb_bound                   200
% 7.79/1.43  --lt_threshold                          2000
% 7.79/1.43  --clause_weak_htbl                      true
% 7.79/1.43  --gc_record_bc_elim                     false
% 7.79/1.43  
% 7.79/1.43  ------ Preprocessing Options
% 7.79/1.43  
% 7.79/1.43  --preprocessing_flag                    true
% 7.79/1.43  --time_out_prep_mult                    0.1
% 7.79/1.43  --splitting_mode                        input
% 7.79/1.43  --splitting_grd                         true
% 7.79/1.43  --splitting_cvd                         false
% 7.79/1.43  --splitting_cvd_svl                     false
% 7.79/1.43  --splitting_nvd                         32
% 7.79/1.43  --sub_typing                            true
% 7.79/1.43  --prep_gs_sim                           true
% 7.79/1.43  --prep_unflatten                        true
% 7.79/1.43  --prep_res_sim                          true
% 7.79/1.43  --prep_upred                            true
% 7.79/1.43  --prep_sem_filter                       exhaustive
% 7.79/1.43  --prep_sem_filter_out                   false
% 7.79/1.43  --pred_elim                             true
% 7.79/1.43  --res_sim_input                         true
% 7.79/1.43  --eq_ax_congr_red                       true
% 7.79/1.43  --pure_diseq_elim                       true
% 7.79/1.43  --brand_transform                       false
% 7.79/1.43  --non_eq_to_eq                          false
% 7.79/1.43  --prep_def_merge                        true
% 7.79/1.43  --prep_def_merge_prop_impl              false
% 7.79/1.43  --prep_def_merge_mbd                    true
% 7.79/1.43  --prep_def_merge_tr_red                 false
% 7.79/1.43  --prep_def_merge_tr_cl                  false
% 7.79/1.43  --smt_preprocessing                     true
% 7.79/1.43  --smt_ac_axioms                         fast
% 7.79/1.43  --preprocessed_out                      false
% 7.79/1.43  --preprocessed_stats                    false
% 7.79/1.43  
% 7.79/1.43  ------ Abstraction refinement Options
% 7.79/1.43  
% 7.79/1.43  --abstr_ref                             []
% 7.79/1.43  --abstr_ref_prep                        false
% 7.79/1.43  --abstr_ref_until_sat                   false
% 7.79/1.43  --abstr_ref_sig_restrict                funpre
% 7.79/1.43  --abstr_ref_af_restrict_to_split_sk     false
% 7.79/1.43  --abstr_ref_under                       []
% 7.79/1.43  
% 7.79/1.43  ------ SAT Options
% 7.79/1.43  
% 7.79/1.43  --sat_mode                              false
% 7.79/1.43  --sat_fm_restart_options                ""
% 7.79/1.43  --sat_gr_def                            false
% 7.79/1.43  --sat_epr_types                         true
% 7.79/1.43  --sat_non_cyclic_types                  false
% 7.79/1.43  --sat_finite_models                     false
% 7.79/1.43  --sat_fm_lemmas                         false
% 7.79/1.43  --sat_fm_prep                           false
% 7.79/1.43  --sat_fm_uc_incr                        true
% 7.79/1.43  --sat_out_model                         small
% 7.79/1.43  --sat_out_clauses                       false
% 7.79/1.43  
% 7.79/1.43  ------ QBF Options
% 7.79/1.43  
% 7.79/1.43  --qbf_mode                              false
% 7.79/1.43  --qbf_elim_univ                         false
% 7.79/1.43  --qbf_dom_inst                          none
% 7.79/1.43  --qbf_dom_pre_inst                      false
% 7.79/1.43  --qbf_sk_in                             false
% 7.79/1.43  --qbf_pred_elim                         true
% 7.79/1.43  --qbf_split                             512
% 7.79/1.43  
% 7.79/1.43  ------ BMC1 Options
% 7.79/1.43  
% 7.79/1.43  --bmc1_incremental                      false
% 7.79/1.43  --bmc1_axioms                           reachable_all
% 7.79/1.43  --bmc1_min_bound                        0
% 7.79/1.43  --bmc1_max_bound                        -1
% 7.79/1.43  --bmc1_max_bound_default                -1
% 7.79/1.43  --bmc1_symbol_reachability              true
% 7.79/1.43  --bmc1_property_lemmas                  false
% 7.79/1.43  --bmc1_k_induction                      false
% 7.79/1.43  --bmc1_non_equiv_states                 false
% 7.79/1.43  --bmc1_deadlock                         false
% 7.79/1.43  --bmc1_ucm                              false
% 7.79/1.43  --bmc1_add_unsat_core                   none
% 7.79/1.43  --bmc1_unsat_core_children              false
% 7.79/1.43  --bmc1_unsat_core_extrapolate_axioms    false
% 7.79/1.43  --bmc1_out_stat                         full
% 7.79/1.43  --bmc1_ground_init                      false
% 7.79/1.43  --bmc1_pre_inst_next_state              false
% 7.79/1.43  --bmc1_pre_inst_state                   false
% 7.79/1.43  --bmc1_pre_inst_reach_state             false
% 7.79/1.43  --bmc1_out_unsat_core                   false
% 7.79/1.43  --bmc1_aig_witness_out                  false
% 7.79/1.43  --bmc1_verbose                          false
% 7.79/1.43  --bmc1_dump_clauses_tptp                false
% 7.79/1.43  --bmc1_dump_unsat_core_tptp             false
% 7.79/1.43  --bmc1_dump_file                        -
% 7.79/1.43  --bmc1_ucm_expand_uc_limit              128
% 7.79/1.43  --bmc1_ucm_n_expand_iterations          6
% 7.79/1.43  --bmc1_ucm_extend_mode                  1
% 7.79/1.43  --bmc1_ucm_init_mode                    2
% 7.79/1.43  --bmc1_ucm_cone_mode                    none
% 7.79/1.43  --bmc1_ucm_reduced_relation_type        0
% 7.79/1.43  --bmc1_ucm_relax_model                  4
% 7.79/1.43  --bmc1_ucm_full_tr_after_sat            true
% 7.79/1.43  --bmc1_ucm_expand_neg_assumptions       false
% 7.79/1.43  --bmc1_ucm_layered_model                none
% 7.79/1.43  --bmc1_ucm_max_lemma_size               10
% 7.79/1.43  
% 7.79/1.43  ------ AIG Options
% 7.79/1.43  
% 7.79/1.43  --aig_mode                              false
% 7.79/1.43  
% 7.79/1.43  ------ Instantiation Options
% 7.79/1.43  
% 7.79/1.43  --instantiation_flag                    true
% 7.79/1.43  --inst_sos_flag                         true
% 7.79/1.43  --inst_sos_phase                        true
% 7.79/1.43  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.79/1.43  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.79/1.43  --inst_lit_sel_side                     num_symb
% 7.79/1.43  --inst_solver_per_active                1400
% 7.79/1.43  --inst_solver_calls_frac                1.
% 7.79/1.43  --inst_passive_queue_type               priority_queues
% 7.79/1.43  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.79/1.43  --inst_passive_queues_freq              [25;2]
% 7.79/1.43  --inst_dismatching                      true
% 7.79/1.43  --inst_eager_unprocessed_to_passive     true
% 7.79/1.43  --inst_prop_sim_given                   true
% 7.79/1.43  --inst_prop_sim_new                     false
% 7.79/1.43  --inst_subs_new                         false
% 7.79/1.43  --inst_eq_res_simp                      false
% 7.79/1.43  --inst_subs_given                       false
% 7.79/1.43  --inst_orphan_elimination               true
% 7.79/1.43  --inst_learning_loop_flag               true
% 7.79/1.43  --inst_learning_start                   3000
% 7.79/1.43  --inst_learning_factor                  2
% 7.79/1.43  --inst_start_prop_sim_after_learn       3
% 7.79/1.43  --inst_sel_renew                        solver
% 7.79/1.43  --inst_lit_activity_flag                true
% 7.79/1.43  --inst_restr_to_given                   false
% 7.79/1.43  --inst_activity_threshold               500
% 7.79/1.43  --inst_out_proof                        true
% 7.79/1.43  
% 7.79/1.43  ------ Resolution Options
% 7.79/1.43  
% 7.79/1.43  --resolution_flag                       true
% 7.79/1.43  --res_lit_sel                           adaptive
% 7.79/1.43  --res_lit_sel_side                      none
% 7.79/1.43  --res_ordering                          kbo
% 7.79/1.43  --res_to_prop_solver                    active
% 7.79/1.43  --res_prop_simpl_new                    false
% 7.79/1.43  --res_prop_simpl_given                  true
% 7.79/1.43  --res_passive_queue_type                priority_queues
% 7.79/1.43  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.79/1.43  --res_passive_queues_freq               [15;5]
% 7.79/1.43  --res_forward_subs                      full
% 7.79/1.43  --res_backward_subs                     full
% 7.79/1.43  --res_forward_subs_resolution           true
% 7.79/1.43  --res_backward_subs_resolution          true
% 7.79/1.43  --res_orphan_elimination                true
% 7.79/1.43  --res_time_limit                        2.
% 7.79/1.43  --res_out_proof                         true
% 7.79/1.43  
% 7.79/1.43  ------ Superposition Options
% 7.79/1.43  
% 7.79/1.43  --superposition_flag                    true
% 7.79/1.43  --sup_passive_queue_type                priority_queues
% 7.79/1.43  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.79/1.43  --sup_passive_queues_freq               [8;1;4]
% 7.79/1.43  --demod_completeness_check              fast
% 7.79/1.43  --demod_use_ground                      true
% 7.79/1.43  --sup_to_prop_solver                    passive
% 7.79/1.43  --sup_prop_simpl_new                    true
% 7.79/1.43  --sup_prop_simpl_given                  true
% 7.79/1.43  --sup_fun_splitting                     true
% 7.79/1.43  --sup_smt_interval                      50000
% 7.79/1.43  
% 7.79/1.43  ------ Superposition Simplification Setup
% 7.79/1.43  
% 7.79/1.43  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.79/1.43  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.79/1.43  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.43  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.79/1.43  --sup_full_triv                         [TrivRules;PropSubs]
% 7.79/1.43  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.79/1.43  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.79/1.43  --sup_immed_triv                        [TrivRules]
% 7.79/1.43  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.43  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.43  --sup_immed_bw_main                     []
% 7.79/1.43  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.79/1.43  --sup_input_triv                        [Unflattening;TrivRules]
% 7.79/1.43  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.43  --sup_input_bw                          []
% 7.79/1.43  
% 7.79/1.43  ------ Combination Options
% 7.79/1.43  
% 7.79/1.43  --comb_res_mult                         3
% 7.79/1.43  --comb_sup_mult                         2
% 7.79/1.43  --comb_inst_mult                        10
% 7.79/1.43  
% 7.79/1.43  ------ Debug Options
% 7.79/1.43  
% 7.79/1.43  --dbg_backtrace                         false
% 7.79/1.43  --dbg_dump_prop_clauses                 false
% 7.79/1.43  --dbg_dump_prop_clauses_file            -
% 7.79/1.43  --dbg_out_stat                          false
% 7.79/1.43  ------ Parsing...
% 7.79/1.43  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.79/1.43  
% 7.79/1.43  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.79/1.43  
% 7.79/1.43  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.79/1.43  
% 7.79/1.43  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.79/1.43  ------ Proving...
% 7.79/1.43  ------ Problem Properties 
% 7.79/1.43  
% 7.79/1.43  
% 7.79/1.43  clauses                                 41
% 7.79/1.43  conjectures                             11
% 7.79/1.43  EPR                                     18
% 7.79/1.43  Horn                                    31
% 7.79/1.43  unary                                   11
% 7.79/1.43  binary                                  7
% 7.79/1.43  lits                                    133
% 7.79/1.43  lits eq                                 8
% 7.79/1.43  fd_pure                                 0
% 7.79/1.43  fd_pseudo                               0
% 7.79/1.43  fd_cond                                 0
% 7.79/1.43  fd_pseudo_cond                          2
% 7.79/1.43  AC symbols                              0
% 7.79/1.43  
% 7.79/1.43  ------ Schedule dynamic 5 is on 
% 7.79/1.43  
% 7.79/1.43  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.79/1.43  
% 7.79/1.43  
% 7.79/1.43  ------ 
% 7.79/1.43  Current options:
% 7.79/1.43  ------ 
% 7.79/1.43  
% 7.79/1.43  ------ Input Options
% 7.79/1.43  
% 7.79/1.43  --out_options                           all
% 7.79/1.43  --tptp_safe_out                         true
% 7.79/1.43  --problem_path                          ""
% 7.79/1.43  --include_path                          ""
% 7.79/1.43  --clausifier                            res/vclausify_rel
% 7.79/1.43  --clausifier_options                    ""
% 7.79/1.43  --stdin                                 false
% 7.79/1.43  --stats_out                             all
% 7.79/1.43  
% 7.79/1.43  ------ General Options
% 7.79/1.43  
% 7.79/1.43  --fof                                   false
% 7.79/1.43  --time_out_real                         305.
% 7.79/1.43  --time_out_virtual                      -1.
% 7.79/1.43  --symbol_type_check                     false
% 7.79/1.43  --clausify_out                          false
% 7.79/1.43  --sig_cnt_out                           false
% 7.79/1.43  --trig_cnt_out                          false
% 7.79/1.43  --trig_cnt_out_tolerance                1.
% 7.79/1.43  --trig_cnt_out_sk_spl                   false
% 7.79/1.43  --abstr_cl_out                          false
% 7.79/1.43  
% 7.79/1.43  ------ Global Options
% 7.79/1.43  
% 7.79/1.43  --schedule                              default
% 7.79/1.43  --add_important_lit                     false
% 7.79/1.43  --prop_solver_per_cl                    1000
% 7.79/1.43  --min_unsat_core                        false
% 7.79/1.43  --soft_assumptions                      false
% 7.79/1.43  --soft_lemma_size                       3
% 7.79/1.43  --prop_impl_unit_size                   0
% 7.79/1.43  --prop_impl_unit                        []
% 7.79/1.43  --share_sel_clauses                     true
% 7.79/1.43  --reset_solvers                         false
% 7.79/1.43  --bc_imp_inh                            [conj_cone]
% 7.79/1.43  --conj_cone_tolerance                   3.
% 7.79/1.43  --extra_neg_conj                        none
% 7.79/1.43  --large_theory_mode                     true
% 7.79/1.43  --prolific_symb_bound                   200
% 7.79/1.43  --lt_threshold                          2000
% 7.79/1.43  --clause_weak_htbl                      true
% 7.79/1.43  --gc_record_bc_elim                     false
% 7.79/1.43  
% 7.79/1.43  ------ Preprocessing Options
% 7.79/1.43  
% 7.79/1.43  --preprocessing_flag                    true
% 7.79/1.43  --time_out_prep_mult                    0.1
% 7.79/1.43  --splitting_mode                        input
% 7.79/1.43  --splitting_grd                         true
% 7.79/1.43  --splitting_cvd                         false
% 7.79/1.43  --splitting_cvd_svl                     false
% 7.79/1.43  --splitting_nvd                         32
% 7.79/1.43  --sub_typing                            true
% 7.79/1.43  --prep_gs_sim                           true
% 7.79/1.43  --prep_unflatten                        true
% 7.79/1.43  --prep_res_sim                          true
% 7.79/1.43  --prep_upred                            true
% 7.79/1.43  --prep_sem_filter                       exhaustive
% 7.79/1.43  --prep_sem_filter_out                   false
% 7.79/1.43  --pred_elim                             true
% 7.79/1.43  --res_sim_input                         true
% 7.79/1.43  --eq_ax_congr_red                       true
% 7.79/1.43  --pure_diseq_elim                       true
% 7.79/1.43  --brand_transform                       false
% 7.79/1.43  --non_eq_to_eq                          false
% 7.79/1.43  --prep_def_merge                        true
% 7.79/1.43  --prep_def_merge_prop_impl              false
% 7.79/1.43  --prep_def_merge_mbd                    true
% 7.79/1.43  --prep_def_merge_tr_red                 false
% 7.79/1.43  --prep_def_merge_tr_cl                  false
% 7.79/1.43  --smt_preprocessing                     true
% 7.79/1.43  --smt_ac_axioms                         fast
% 7.79/1.43  --preprocessed_out                      false
% 7.79/1.43  --preprocessed_stats                    false
% 7.79/1.43  
% 7.79/1.43  ------ Abstraction refinement Options
% 7.79/1.43  
% 7.79/1.43  --abstr_ref                             []
% 7.79/1.43  --abstr_ref_prep                        false
% 7.79/1.43  --abstr_ref_until_sat                   false
% 7.79/1.43  --abstr_ref_sig_restrict                funpre
% 7.79/1.43  --abstr_ref_af_restrict_to_split_sk     false
% 7.79/1.43  --abstr_ref_under                       []
% 7.79/1.43  
% 7.79/1.43  ------ SAT Options
% 7.79/1.43  
% 7.79/1.43  --sat_mode                              false
% 7.79/1.43  --sat_fm_restart_options                ""
% 7.79/1.43  --sat_gr_def                            false
% 7.79/1.43  --sat_epr_types                         true
% 7.79/1.43  --sat_non_cyclic_types                  false
% 7.79/1.43  --sat_finite_models                     false
% 7.79/1.43  --sat_fm_lemmas                         false
% 7.79/1.43  --sat_fm_prep                           false
% 7.79/1.43  --sat_fm_uc_incr                        true
% 7.79/1.43  --sat_out_model                         small
% 7.79/1.43  --sat_out_clauses                       false
% 7.79/1.43  
% 7.79/1.43  ------ QBF Options
% 7.79/1.43  
% 7.79/1.43  --qbf_mode                              false
% 7.79/1.43  --qbf_elim_univ                         false
% 7.79/1.43  --qbf_dom_inst                          none
% 7.79/1.43  --qbf_dom_pre_inst                      false
% 7.79/1.43  --qbf_sk_in                             false
% 7.79/1.43  --qbf_pred_elim                         true
% 7.79/1.43  --qbf_split                             512
% 7.79/1.43  
% 7.79/1.43  ------ BMC1 Options
% 7.79/1.43  
% 7.79/1.43  --bmc1_incremental                      false
% 7.79/1.43  --bmc1_axioms                           reachable_all
% 7.79/1.43  --bmc1_min_bound                        0
% 7.79/1.43  --bmc1_max_bound                        -1
% 7.79/1.43  --bmc1_max_bound_default                -1
% 7.79/1.43  --bmc1_symbol_reachability              true
% 7.79/1.43  --bmc1_property_lemmas                  false
% 7.79/1.43  --bmc1_k_induction                      false
% 7.79/1.43  --bmc1_non_equiv_states                 false
% 7.79/1.43  --bmc1_deadlock                         false
% 7.79/1.43  --bmc1_ucm                              false
% 7.79/1.43  --bmc1_add_unsat_core                   none
% 7.79/1.43  --bmc1_unsat_core_children              false
% 7.79/1.43  --bmc1_unsat_core_extrapolate_axioms    false
% 7.79/1.43  --bmc1_out_stat                         full
% 7.79/1.43  --bmc1_ground_init                      false
% 7.79/1.43  --bmc1_pre_inst_next_state              false
% 7.79/1.43  --bmc1_pre_inst_state                   false
% 7.79/1.43  --bmc1_pre_inst_reach_state             false
% 7.79/1.43  --bmc1_out_unsat_core                   false
% 7.79/1.43  --bmc1_aig_witness_out                  false
% 7.79/1.43  --bmc1_verbose                          false
% 7.79/1.43  --bmc1_dump_clauses_tptp                false
% 7.79/1.43  --bmc1_dump_unsat_core_tptp             false
% 7.79/1.43  --bmc1_dump_file                        -
% 7.79/1.43  --bmc1_ucm_expand_uc_limit              128
% 7.79/1.43  --bmc1_ucm_n_expand_iterations          6
% 7.79/1.43  --bmc1_ucm_extend_mode                  1
% 7.79/1.43  --bmc1_ucm_init_mode                    2
% 7.79/1.43  --bmc1_ucm_cone_mode                    none
% 7.79/1.43  --bmc1_ucm_reduced_relation_type        0
% 7.79/1.43  --bmc1_ucm_relax_model                  4
% 7.79/1.43  --bmc1_ucm_full_tr_after_sat            true
% 7.79/1.43  --bmc1_ucm_expand_neg_assumptions       false
% 7.79/1.43  --bmc1_ucm_layered_model                none
% 7.79/1.43  --bmc1_ucm_max_lemma_size               10
% 7.79/1.43  
% 7.79/1.43  ------ AIG Options
% 7.79/1.43  
% 7.79/1.43  --aig_mode                              false
% 7.79/1.43  
% 7.79/1.43  ------ Instantiation Options
% 7.79/1.43  
% 7.79/1.43  --instantiation_flag                    true
% 7.79/1.43  --inst_sos_flag                         true
% 7.79/1.43  --inst_sos_phase                        true
% 7.79/1.43  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.79/1.43  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.79/1.43  --inst_lit_sel_side                     none
% 7.79/1.43  --inst_solver_per_active                1400
% 7.79/1.43  --inst_solver_calls_frac                1.
% 7.79/1.43  --inst_passive_queue_type               priority_queues
% 7.79/1.43  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.79/1.43  --inst_passive_queues_freq              [25;2]
% 7.79/1.43  --inst_dismatching                      true
% 7.79/1.43  --inst_eager_unprocessed_to_passive     true
% 7.79/1.43  --inst_prop_sim_given                   true
% 7.79/1.43  --inst_prop_sim_new                     false
% 7.79/1.43  --inst_subs_new                         false
% 7.79/1.43  --inst_eq_res_simp                      false
% 7.79/1.43  --inst_subs_given                       false
% 7.79/1.43  --inst_orphan_elimination               true
% 7.79/1.43  --inst_learning_loop_flag               true
% 7.79/1.43  --inst_learning_start                   3000
% 7.79/1.43  --inst_learning_factor                  2
% 7.79/1.43  --inst_start_prop_sim_after_learn       3
% 7.79/1.43  --inst_sel_renew                        solver
% 7.79/1.43  --inst_lit_activity_flag                true
% 7.79/1.43  --inst_restr_to_given                   false
% 7.79/1.43  --inst_activity_threshold               500
% 7.79/1.43  --inst_out_proof                        true
% 7.79/1.43  
% 7.79/1.43  ------ Resolution Options
% 7.79/1.43  
% 7.79/1.43  --resolution_flag                       false
% 7.79/1.43  --res_lit_sel                           adaptive
% 7.79/1.43  --res_lit_sel_side                      none
% 7.79/1.43  --res_ordering                          kbo
% 7.79/1.43  --res_to_prop_solver                    active
% 7.79/1.43  --res_prop_simpl_new                    false
% 7.79/1.43  --res_prop_simpl_given                  true
% 7.79/1.43  --res_passive_queue_type                priority_queues
% 7.79/1.43  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.79/1.43  --res_passive_queues_freq               [15;5]
% 7.79/1.43  --res_forward_subs                      full
% 7.79/1.43  --res_backward_subs                     full
% 7.79/1.43  --res_forward_subs_resolution           true
% 7.79/1.43  --res_backward_subs_resolution          true
% 7.79/1.43  --res_orphan_elimination                true
% 7.79/1.43  --res_time_limit                        2.
% 7.79/1.43  --res_out_proof                         true
% 7.79/1.43  
% 7.79/1.43  ------ Superposition Options
% 7.79/1.43  
% 7.79/1.43  --superposition_flag                    true
% 7.79/1.43  --sup_passive_queue_type                priority_queues
% 7.79/1.43  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.79/1.43  --sup_passive_queues_freq               [8;1;4]
% 7.79/1.43  --demod_completeness_check              fast
% 7.79/1.43  --demod_use_ground                      true
% 7.79/1.43  --sup_to_prop_solver                    passive
% 7.79/1.43  --sup_prop_simpl_new                    true
% 7.79/1.43  --sup_prop_simpl_given                  true
% 7.79/1.43  --sup_fun_splitting                     true
% 7.79/1.43  --sup_smt_interval                      50000
% 7.79/1.43  
% 7.79/1.43  ------ Superposition Simplification Setup
% 7.79/1.43  
% 7.79/1.43  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.79/1.43  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.79/1.43  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.43  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.79/1.43  --sup_full_triv                         [TrivRules;PropSubs]
% 7.79/1.43  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.79/1.43  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.79/1.43  --sup_immed_triv                        [TrivRules]
% 7.79/1.43  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.43  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.43  --sup_immed_bw_main                     []
% 7.79/1.43  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.79/1.43  --sup_input_triv                        [Unflattening;TrivRules]
% 7.79/1.43  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.43  --sup_input_bw                          []
% 7.79/1.43  
% 7.79/1.43  ------ Combination Options
% 7.79/1.43  
% 7.79/1.43  --comb_res_mult                         3
% 7.79/1.43  --comb_sup_mult                         2
% 7.79/1.43  --comb_inst_mult                        10
% 7.79/1.43  
% 7.79/1.43  ------ Debug Options
% 7.79/1.43  
% 7.79/1.43  --dbg_backtrace                         false
% 7.79/1.43  --dbg_dump_prop_clauses                 false
% 7.79/1.43  --dbg_dump_prop_clauses_file            -
% 7.79/1.43  --dbg_out_stat                          false
% 7.79/1.43  
% 7.79/1.43  
% 7.79/1.43  
% 7.79/1.43  
% 7.79/1.43  ------ Proving...
% 7.79/1.43  
% 7.79/1.43  
% 7.79/1.43  % SZS status Theorem for theBenchmark.p
% 7.79/1.43  
% 7.79/1.43  % SZS output start CNFRefutation for theBenchmark.p
% 7.79/1.43  
% 7.79/1.43  fof(f13,conjecture,(
% 7.79/1.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 7.79/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.43  
% 7.79/1.43  fof(f14,negated_conjecture,(
% 7.79/1.43    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 7.79/1.43    inference(negated_conjecture,[],[f13])).
% 7.79/1.43  
% 7.79/1.43  fof(f15,plain,(
% 7.79/1.43    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 7.79/1.43    inference(pure_predicate_removal,[],[f14])).
% 7.79/1.43  
% 7.79/1.43  fof(f30,plain,(
% 7.79/1.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.79/1.43    inference(ennf_transformation,[],[f15])).
% 7.79/1.43  
% 7.79/1.43  fof(f31,plain,(
% 7.79/1.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.79/1.43    inference(flattening,[],[f30])).
% 7.79/1.43  
% 7.79/1.43  fof(f50,plain,(
% 7.79/1.43    ( ! [X2,X0,X1] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((r1_tsep_1(sK8,X2) | r1_tsep_1(X2,sK8)) & (~r1_tsep_1(sK8,X1) | ~r1_tsep_1(X1,sK8)) & m1_pre_topc(X1,X2) & m1_pre_topc(sK8,X0) & ~v2_struct_0(sK8))) )),
% 7.79/1.43    introduced(choice_axiom,[])).
% 7.79/1.43  
% 7.79/1.43  fof(f49,plain,(
% 7.79/1.43    ( ! [X0,X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : ((r1_tsep_1(X3,sK7) | r1_tsep_1(sK7,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,sK7) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK7,X0) & ~v2_struct_0(sK7))) )),
% 7.79/1.43    introduced(choice_axiom,[])).
% 7.79/1.43  
% 7.79/1.43  fof(f48,plain,(
% 7.79/1.43    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK6) | ~r1_tsep_1(sK6,X3)) & m1_pre_topc(sK6,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 7.79/1.43    introduced(choice_axiom,[])).
% 7.79/1.43  
% 7.79/1.43  fof(f47,plain,(
% 7.79/1.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK5) & ~v2_struct_0(X1)) & l1_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 7.79/1.43    introduced(choice_axiom,[])).
% 7.79/1.43  
% 7.79/1.43  fof(f51,plain,(
% 7.79/1.43    ((((r1_tsep_1(sK8,sK7) | r1_tsep_1(sK7,sK8)) & (~r1_tsep_1(sK8,sK6) | ~r1_tsep_1(sK6,sK8)) & m1_pre_topc(sK6,sK7) & m1_pre_topc(sK8,sK5) & ~v2_struct_0(sK8)) & m1_pre_topc(sK7,sK5) & ~v2_struct_0(sK7)) & m1_pre_topc(sK6,sK5) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 7.79/1.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f31,f50,f49,f48,f47])).
% 7.79/1.43  
% 7.79/1.43  fof(f89,plain,(
% 7.79/1.43    m1_pre_topc(sK7,sK5)),
% 7.79/1.43    inference(cnf_transformation,[],[f51])).
% 7.79/1.43  
% 7.79/1.43  fof(f8,axiom,(
% 7.79/1.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.79/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.43  
% 7.79/1.43  fof(f22,plain,(
% 7.79/1.43    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.79/1.43    inference(ennf_transformation,[],[f8])).
% 7.79/1.43  
% 7.79/1.43  fof(f75,plain,(
% 7.79/1.43    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.79/1.43    inference(cnf_transformation,[],[f22])).
% 7.79/1.43  
% 7.79/1.43  fof(f85,plain,(
% 7.79/1.43    l1_pre_topc(sK5)),
% 7.79/1.43    inference(cnf_transformation,[],[f51])).
% 7.79/1.43  
% 7.79/1.43  fof(f7,axiom,(
% 7.79/1.43    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.79/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.43  
% 7.79/1.43  fof(f21,plain,(
% 7.79/1.43    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.79/1.43    inference(ennf_transformation,[],[f7])).
% 7.79/1.43  
% 7.79/1.43  fof(f74,plain,(
% 7.79/1.43    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.79/1.43    inference(cnf_transformation,[],[f21])).
% 7.79/1.43  
% 7.79/1.43  fof(f5,axiom,(
% 7.79/1.43    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.79/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.43  
% 7.79/1.43  fof(f19,plain,(
% 7.79/1.43    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.79/1.43    inference(ennf_transformation,[],[f5])).
% 7.79/1.43  
% 7.79/1.43  fof(f60,plain,(
% 7.79/1.43    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.79/1.43    inference(cnf_transformation,[],[f19])).
% 7.79/1.43  
% 7.79/1.43  fof(f10,axiom,(
% 7.79/1.43    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 7.79/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.43  
% 7.79/1.43  fof(f25,plain,(
% 7.79/1.43    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 7.79/1.43    inference(ennf_transformation,[],[f10])).
% 7.79/1.43  
% 7.79/1.43  fof(f46,plain,(
% 7.79/1.43    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 7.79/1.43    inference(nnf_transformation,[],[f25])).
% 7.79/1.43  
% 7.79/1.43  fof(f78,plain,(
% 7.79/1.43    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 7.79/1.43    inference(cnf_transformation,[],[f46])).
% 7.79/1.43  
% 7.79/1.43  fof(f92,plain,(
% 7.79/1.43    m1_pre_topc(sK6,sK7)),
% 7.79/1.43    inference(cnf_transformation,[],[f51])).
% 7.79/1.43  
% 7.79/1.43  fof(f6,axiom,(
% 7.79/1.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 7.79/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.43  
% 7.79/1.43  fof(f20,plain,(
% 7.79/1.43    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.79/1.43    inference(ennf_transformation,[],[f6])).
% 7.79/1.43  
% 7.79/1.43  fof(f33,plain,(
% 7.79/1.43    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 7.79/1.43    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 7.79/1.43  
% 7.79/1.43  fof(f32,plain,(
% 7.79/1.43    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 7.79/1.43    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.79/1.43  
% 7.79/1.43  fof(f34,plain,(
% 7.79/1.43    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.79/1.43    inference(definition_folding,[],[f20,f33,f32])).
% 7.79/1.43  
% 7.79/1.43  fof(f73,plain,(
% 7.79/1.43    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.79/1.43    inference(cnf_transformation,[],[f34])).
% 7.79/1.43  
% 7.79/1.43  fof(f37,plain,(
% 7.79/1.43    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 7.79/1.43    inference(nnf_transformation,[],[f33])).
% 7.79/1.43  
% 7.79/1.43  fof(f61,plain,(
% 7.79/1.43    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 7.79/1.43    inference(cnf_transformation,[],[f37])).
% 7.79/1.43  
% 7.79/1.43  fof(f38,plain,(
% 7.79/1.43    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 7.79/1.43    inference(nnf_transformation,[],[f32])).
% 7.79/1.43  
% 7.79/1.43  fof(f39,plain,(
% 7.79/1.43    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 7.79/1.43    inference(flattening,[],[f38])).
% 7.79/1.43  
% 7.79/1.43  fof(f40,plain,(
% 7.79/1.43    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 7.79/1.43    inference(rectify,[],[f39])).
% 7.79/1.43  
% 7.79/1.43  fof(f43,plain,(
% 7.79/1.43    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 7.79/1.43    introduced(choice_axiom,[])).
% 7.79/1.43  
% 7.79/1.43  fof(f42,plain,(
% 7.79/1.43    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 7.79/1.43    introduced(choice_axiom,[])).
% 7.79/1.43  
% 7.79/1.43  fof(f41,plain,(
% 7.79/1.43    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.79/1.43    introduced(choice_axiom,[])).
% 7.79/1.43  
% 7.79/1.43  fof(f44,plain,(
% 7.79/1.43    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 7.79/1.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f40,f43,f42,f41])).
% 7.79/1.43  
% 7.79/1.43  fof(f63,plain,(
% 7.79/1.43    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 7.79/1.43    inference(cnf_transformation,[],[f44])).
% 7.79/1.43  
% 7.79/1.43  fof(f4,axiom,(
% 7.79/1.43    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 7.79/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.43  
% 7.79/1.43  fof(f17,plain,(
% 7.79/1.43    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 7.79/1.43    inference(ennf_transformation,[],[f4])).
% 7.79/1.43  
% 7.79/1.43  fof(f18,plain,(
% 7.79/1.43    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 7.79/1.43    inference(flattening,[],[f17])).
% 7.79/1.43  
% 7.79/1.43  fof(f59,plain,(
% 7.79/1.43    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.79/1.43    inference(cnf_transformation,[],[f18])).
% 7.79/1.43  
% 7.79/1.43  fof(f3,axiom,(
% 7.79/1.43    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.79/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.43  
% 7.79/1.43  fof(f58,plain,(
% 7.79/1.43    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.79/1.43    inference(cnf_transformation,[],[f3])).
% 7.79/1.43  
% 7.79/1.43  fof(f1,axiom,(
% 7.79/1.43    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.79/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.43  
% 7.79/1.43  fof(f35,plain,(
% 7.79/1.43    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.79/1.43    inference(nnf_transformation,[],[f1])).
% 7.79/1.43  
% 7.79/1.43  fof(f36,plain,(
% 7.79/1.43    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.79/1.43    inference(flattening,[],[f35])).
% 7.79/1.43  
% 7.79/1.43  fof(f54,plain,(
% 7.79/1.43    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.79/1.43    inference(cnf_transformation,[],[f36])).
% 7.79/1.43  
% 7.79/1.43  fof(f52,plain,(
% 7.79/1.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.79/1.43    inference(cnf_transformation,[],[f36])).
% 7.79/1.43  
% 7.79/1.43  fof(f96,plain,(
% 7.79/1.43    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.79/1.43    inference(equality_resolution,[],[f52])).
% 7.79/1.43  
% 7.79/1.43  fof(f2,axiom,(
% 7.79/1.43    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.79/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.43  
% 7.79/1.43  fof(f16,plain,(
% 7.79/1.43    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.79/1.43    inference(ennf_transformation,[],[f2])).
% 7.79/1.43  
% 7.79/1.43  fof(f57,plain,(
% 7.79/1.43    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 7.79/1.43    inference(cnf_transformation,[],[f16])).
% 7.79/1.43  
% 7.79/1.43  fof(f87,plain,(
% 7.79/1.43    m1_pre_topc(sK6,sK5)),
% 7.79/1.43    inference(cnf_transformation,[],[f51])).
% 7.79/1.43  
% 7.79/1.43  fof(f79,plain,(
% 7.79/1.43    ( ! [X0,X1] : (r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 7.79/1.43    inference(cnf_transformation,[],[f46])).
% 7.79/1.43  
% 7.79/1.43  fof(f94,plain,(
% 7.79/1.43    r1_tsep_1(sK8,sK7) | r1_tsep_1(sK7,sK8)),
% 7.79/1.43    inference(cnf_transformation,[],[f51])).
% 7.79/1.43  
% 7.79/1.43  fof(f12,axiom,(
% 7.79/1.43    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 7.79/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.43  
% 7.79/1.43  fof(f28,plain,(
% 7.79/1.43    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 7.79/1.43    inference(ennf_transformation,[],[f12])).
% 7.79/1.43  
% 7.79/1.43  fof(f29,plain,(
% 7.79/1.43    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 7.79/1.43    inference(flattening,[],[f28])).
% 7.79/1.43  
% 7.79/1.43  fof(f83,plain,(
% 7.79/1.43    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 7.79/1.43    inference(cnf_transformation,[],[f29])).
% 7.79/1.43  
% 7.79/1.43  fof(f93,plain,(
% 7.79/1.43    ~r1_tsep_1(sK8,sK6) | ~r1_tsep_1(sK6,sK8)),
% 7.79/1.43    inference(cnf_transformation,[],[f51])).
% 7.79/1.43  
% 7.79/1.43  fof(f91,plain,(
% 7.79/1.43    m1_pre_topc(sK8,sK5)),
% 7.79/1.43    inference(cnf_transformation,[],[f51])).
% 7.79/1.43  
% 7.79/1.43  cnf(c_37,negated_conjecture,
% 7.79/1.43      ( m1_pre_topc(sK7,sK5) ),
% 7.79/1.43      inference(cnf_transformation,[],[f89]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_3368,plain,
% 7.79/1.43      ( m1_pre_topc(sK7,sK5) = iProver_top ),
% 7.79/1.43      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_23,plain,
% 7.79/1.43      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.79/1.43      inference(cnf_transformation,[],[f75]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_3381,plain,
% 7.79/1.43      ( m1_pre_topc(X0,X1) != iProver_top
% 7.79/1.43      | l1_pre_topc(X1) != iProver_top
% 7.79/1.43      | l1_pre_topc(X0) = iProver_top ),
% 7.79/1.43      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_4282,plain,
% 7.79/1.43      ( l1_pre_topc(sK5) != iProver_top
% 7.79/1.43      | l1_pre_topc(sK7) = iProver_top ),
% 7.79/1.43      inference(superposition,[status(thm)],[c_3368,c_3381]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_41,negated_conjecture,
% 7.79/1.43      ( l1_pre_topc(sK5) ),
% 7.79/1.43      inference(cnf_transformation,[],[f85]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_44,plain,
% 7.79/1.43      ( l1_pre_topc(sK5) = iProver_top ),
% 7.79/1.43      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_48,plain,
% 7.79/1.43      ( m1_pre_topc(sK7,sK5) = iProver_top ),
% 7.79/1.43      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_3623,plain,
% 7.79/1.43      ( ~ m1_pre_topc(sK7,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK7) ),
% 7.79/1.43      inference(instantiation,[status(thm)],[c_23]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_3719,plain,
% 7.79/1.43      ( ~ m1_pre_topc(sK7,sK5) | ~ l1_pre_topc(sK5) | l1_pre_topc(sK7) ),
% 7.79/1.43      inference(instantiation,[status(thm)],[c_3623]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_3720,plain,
% 7.79/1.43      ( m1_pre_topc(sK7,sK5) != iProver_top
% 7.79/1.43      | l1_pre_topc(sK5) != iProver_top
% 7.79/1.43      | l1_pre_topc(sK7) = iProver_top ),
% 7.79/1.43      inference(predicate_to_equality,[status(thm)],[c_3719]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_4586,plain,
% 7.79/1.43      ( l1_pre_topc(sK7) = iProver_top ),
% 7.79/1.43      inference(global_propositional_subsumption,
% 7.79/1.43                [status(thm)],
% 7.79/1.43                [c_4282,c_44,c_48,c_3720]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_22,plain,
% 7.79/1.43      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.79/1.43      inference(cnf_transformation,[],[f74]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_3382,plain,
% 7.79/1.43      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 7.79/1.43      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_4590,plain,
% 7.79/1.43      ( l1_struct_0(sK7) = iProver_top ),
% 7.79/1.43      inference(superposition,[status(thm)],[c_4586,c_3382]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_8,plain,
% 7.79/1.43      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.79/1.43      inference(cnf_transformation,[],[f60]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_3393,plain,
% 7.79/1.43      ( u1_struct_0(X0) = k2_struct_0(X0)
% 7.79/1.43      | l1_struct_0(X0) != iProver_top ),
% 7.79/1.43      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_7087,plain,
% 7.79/1.43      ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
% 7.79/1.43      inference(superposition,[status(thm)],[c_4590,c_3393]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_27,plain,
% 7.79/1.43      ( ~ r1_tsep_1(X0,X1)
% 7.79/1.43      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 7.79/1.43      | ~ l1_struct_0(X0)
% 7.79/1.43      | ~ l1_struct_0(X1) ),
% 7.79/1.43      inference(cnf_transformation,[],[f78]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_3378,plain,
% 7.79/1.43      ( r1_tsep_1(X0,X1) != iProver_top
% 7.79/1.43      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 7.79/1.43      | l1_struct_0(X0) != iProver_top
% 7.79/1.43      | l1_struct_0(X1) != iProver_top ),
% 7.79/1.43      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_8322,plain,
% 7.79/1.43      ( r1_tsep_1(X0,sK7) != iProver_top
% 7.79/1.43      | r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK7)) = iProver_top
% 7.79/1.43      | l1_struct_0(X0) != iProver_top
% 7.79/1.43      | l1_struct_0(sK7) != iProver_top ),
% 7.79/1.43      inference(superposition,[status(thm)],[c_7087,c_3378]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_27983,plain,
% 7.79/1.43      ( l1_struct_0(X0) != iProver_top
% 7.79/1.43      | r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK7)) = iProver_top
% 7.79/1.43      | r1_tsep_1(X0,sK7) != iProver_top ),
% 7.79/1.43      inference(global_propositional_subsumption,
% 7.79/1.43                [status(thm)],
% 7.79/1.43                [c_8322,c_4590]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_27984,plain,
% 7.79/1.43      ( r1_tsep_1(X0,sK7) != iProver_top
% 7.79/1.43      | r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK7)) = iProver_top
% 7.79/1.43      | l1_struct_0(X0) != iProver_top ),
% 7.79/1.43      inference(renaming,[status(thm)],[c_27983]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_34,negated_conjecture,
% 7.79/1.43      ( m1_pre_topc(sK6,sK7) ),
% 7.79/1.43      inference(cnf_transformation,[],[f92]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_3371,plain,
% 7.79/1.43      ( m1_pre_topc(sK6,sK7) = iProver_top ),
% 7.79/1.43      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_21,plain,
% 7.79/1.43      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 7.79/1.43      inference(cnf_transformation,[],[f73]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_10,plain,
% 7.79/1.43      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 7.79/1.43      inference(cnf_transformation,[],[f61]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_468,plain,
% 7.79/1.43      ( sP0(X0,X1)
% 7.79/1.43      | ~ m1_pre_topc(X0,X1)
% 7.79/1.43      | ~ l1_pre_topc(X1)
% 7.79/1.43      | ~ l1_pre_topc(X0) ),
% 7.79/1.43      inference(resolution,[status(thm)],[c_21,c_10]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_472,plain,
% 7.79/1.43      ( ~ l1_pre_topc(X1) | ~ m1_pre_topc(X0,X1) | sP0(X0,X1) ),
% 7.79/1.43      inference(global_propositional_subsumption,
% 7.79/1.43                [status(thm)],
% 7.79/1.43                [c_468,c_23]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_473,plain,
% 7.79/1.43      ( sP0(X0,X1) | ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) ),
% 7.79/1.43      inference(renaming,[status(thm)],[c_472]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_3361,plain,
% 7.79/1.43      ( sP0(X0,X1) = iProver_top
% 7.79/1.43      | m1_pre_topc(X0,X1) != iProver_top
% 7.79/1.43      | l1_pre_topc(X1) != iProver_top ),
% 7.79/1.43      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_4089,plain,
% 7.79/1.43      ( sP0(sK6,sK7) = iProver_top | l1_pre_topc(sK7) != iProver_top ),
% 7.79/1.43      inference(superposition,[status(thm)],[c_3371,c_3361]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_4598,plain,
% 7.79/1.43      ( sP0(sK6,sK7) = iProver_top ),
% 7.79/1.43      inference(global_propositional_subsumption,
% 7.79/1.43                [status(thm)],
% 7.79/1.43                [c_4089,c_44,c_48,c_3720]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_20,plain,
% 7.79/1.43      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 7.79/1.43      inference(cnf_transformation,[],[f63]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_3383,plain,
% 7.79/1.43      ( sP0(X0,X1) != iProver_top
% 7.79/1.43      | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) = iProver_top ),
% 7.79/1.43      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_7,plain,
% 7.79/1.43      ( ~ r1_tarski(X0,X1)
% 7.79/1.43      | ~ r1_tarski(X2,X1)
% 7.79/1.43      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 7.79/1.43      inference(cnf_transformation,[],[f59]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_3394,plain,
% 7.79/1.43      ( r1_tarski(X0,X1) != iProver_top
% 7.79/1.43      | r1_tarski(X2,X1) != iProver_top
% 7.79/1.43      | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
% 7.79/1.43      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_6,plain,
% 7.79/1.43      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 7.79/1.43      inference(cnf_transformation,[],[f58]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_3395,plain,
% 7.79/1.43      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 7.79/1.43      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_0,plain,
% 7.79/1.43      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.79/1.43      inference(cnf_transformation,[],[f54]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_3400,plain,
% 7.79/1.43      ( X0 = X1
% 7.79/1.43      | r1_tarski(X0,X1) != iProver_top
% 7.79/1.43      | r1_tarski(X1,X0) != iProver_top ),
% 7.79/1.43      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_4290,plain,
% 7.79/1.43      ( k2_xboole_0(X0,X1) = X0
% 7.79/1.43      | r1_tarski(k2_xboole_0(X0,X1),X0) != iProver_top ),
% 7.79/1.43      inference(superposition,[status(thm)],[c_3395,c_3400]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_9522,plain,
% 7.79/1.43      ( k2_xboole_0(X0,X1) = X0
% 7.79/1.43      | r1_tarski(X0,X0) != iProver_top
% 7.79/1.43      | r1_tarski(X1,X0) != iProver_top ),
% 7.79/1.43      inference(superposition,[status(thm)],[c_3394,c_4290]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_2,plain,
% 7.79/1.43      ( r1_tarski(X0,X0) ),
% 7.79/1.43      inference(cnf_transformation,[],[f96]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_135,plain,
% 7.79/1.43      ( r1_tarski(X0,X0) = iProver_top ),
% 7.79/1.43      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_10966,plain,
% 7.79/1.43      ( k2_xboole_0(X0,X1) = X0 | r1_tarski(X1,X0) != iProver_top ),
% 7.79/1.43      inference(global_propositional_subsumption,
% 7.79/1.43                [status(thm)],
% 7.79/1.43                [c_9522,c_135]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_10973,plain,
% 7.79/1.43      ( k2_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X0)
% 7.79/1.43      | sP0(X1,X0) != iProver_top ),
% 7.79/1.43      inference(superposition,[status(thm)],[c_3383,c_10966]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_11601,plain,
% 7.79/1.43      ( k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6)) = k2_struct_0(sK7) ),
% 7.79/1.43      inference(superposition,[status(thm)],[c_4598,c_10973]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_3,plain,
% 7.79/1.43      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 7.79/1.43      inference(cnf_transformation,[],[f57]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_3398,plain,
% 7.79/1.43      ( r1_xboole_0(X0,X1) = iProver_top
% 7.79/1.43      | r1_xboole_0(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 7.79/1.43      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_11702,plain,
% 7.79/1.43      ( r1_xboole_0(X0,k2_struct_0(sK6)) = iProver_top
% 7.79/1.43      | r1_xboole_0(X0,k2_struct_0(sK7)) != iProver_top ),
% 7.79/1.43      inference(superposition,[status(thm)],[c_11601,c_3398]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_27996,plain,
% 7.79/1.43      ( r1_tsep_1(X0,sK7) != iProver_top
% 7.79/1.43      | r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK6)) = iProver_top
% 7.79/1.43      | l1_struct_0(X0) != iProver_top ),
% 7.79/1.43      inference(superposition,[status(thm)],[c_27984,c_11702]) ).
% 7.79/1.43  
% 7.79/1.43  cnf(c_28003,plain,
% 7.79/1.43      ( r1_tsep_1(sK8,sK7) != iProver_top
% 7.79/1.43      | r1_xboole_0(u1_struct_0(sK8),k2_struct_0(sK6)) = iProver_top
% 7.79/1.44      | l1_struct_0(sK8) != iProver_top ),
% 7.79/1.44      inference(instantiation,[status(thm)],[c_27996]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_4280,plain,
% 7.79/1.44      ( l1_pre_topc(sK6) = iProver_top
% 7.79/1.44      | l1_pre_topc(sK7) != iProver_top ),
% 7.79/1.44      inference(superposition,[status(thm)],[c_3371,c_3381]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_39,negated_conjecture,
% 7.79/1.44      ( m1_pre_topc(sK6,sK5) ),
% 7.79/1.44      inference(cnf_transformation,[],[f87]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_46,plain,
% 7.79/1.44      ( m1_pre_topc(sK6,sK5) = iProver_top ),
% 7.79/1.44      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_3671,plain,
% 7.79/1.44      ( ~ m1_pre_topc(X0,sK5) | l1_pre_topc(X0) | ~ l1_pre_topc(sK5) ),
% 7.79/1.44      inference(instantiation,[status(thm)],[c_23]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_3752,plain,
% 7.79/1.44      ( ~ m1_pre_topc(sK6,sK5) | ~ l1_pre_topc(sK5) | l1_pre_topc(sK6) ),
% 7.79/1.44      inference(instantiation,[status(thm)],[c_3671]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_3753,plain,
% 7.79/1.44      ( m1_pre_topc(sK6,sK5) != iProver_top
% 7.79/1.44      | l1_pre_topc(sK5) != iProver_top
% 7.79/1.44      | l1_pre_topc(sK6) = iProver_top ),
% 7.79/1.44      inference(predicate_to_equality,[status(thm)],[c_3752]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_4442,plain,
% 7.79/1.44      ( l1_pre_topc(sK6) = iProver_top ),
% 7.79/1.44      inference(global_propositional_subsumption,
% 7.79/1.44                [status(thm)],
% 7.79/1.44                [c_4280,c_44,c_46,c_3753]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_4446,plain,
% 7.79/1.44      ( l1_struct_0(sK6) = iProver_top ),
% 7.79/1.44      inference(superposition,[status(thm)],[c_4442,c_3382]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_6163,plain,
% 7.79/1.44      ( u1_struct_0(sK6) = k2_struct_0(sK6) ),
% 7.79/1.44      inference(superposition,[status(thm)],[c_4446,c_3393]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_26,plain,
% 7.79/1.44      ( r1_tsep_1(X0,X1)
% 7.79/1.44      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 7.79/1.44      | ~ l1_struct_0(X0)
% 7.79/1.44      | ~ l1_struct_0(X1) ),
% 7.79/1.44      inference(cnf_transformation,[],[f79]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_3379,plain,
% 7.79/1.44      ( r1_tsep_1(X0,X1) = iProver_top
% 7.79/1.44      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 7.79/1.44      | l1_struct_0(X0) != iProver_top
% 7.79/1.44      | l1_struct_0(X1) != iProver_top ),
% 7.79/1.44      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_7853,plain,
% 7.79/1.44      ( r1_tsep_1(X0,sK6) = iProver_top
% 7.79/1.44      | r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK6)) != iProver_top
% 7.79/1.44      | l1_struct_0(X0) != iProver_top
% 7.79/1.44      | l1_struct_0(sK6) != iProver_top ),
% 7.79/1.44      inference(superposition,[status(thm)],[c_6163,c_3379]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_7880,plain,
% 7.79/1.44      ( r1_tsep_1(sK8,sK6) = iProver_top
% 7.79/1.44      | r1_xboole_0(u1_struct_0(sK8),k2_struct_0(sK6)) != iProver_top
% 7.79/1.44      | l1_struct_0(sK6) != iProver_top
% 7.79/1.44      | l1_struct_0(sK8) != iProver_top ),
% 7.79/1.44      inference(instantiation,[status(thm)],[c_7853]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_32,negated_conjecture,
% 7.79/1.44      ( r1_tsep_1(sK7,sK8) | r1_tsep_1(sK8,sK7) ),
% 7.79/1.44      inference(cnf_transformation,[],[f94]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_3373,plain,
% 7.79/1.44      ( r1_tsep_1(sK7,sK8) = iProver_top
% 7.79/1.44      | r1_tsep_1(sK8,sK7) = iProver_top ),
% 7.79/1.44      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_31,plain,
% 7.79/1.44      ( ~ r1_tsep_1(X0,X1)
% 7.79/1.44      | r1_tsep_1(X1,X0)
% 7.79/1.44      | ~ l1_struct_0(X0)
% 7.79/1.44      | ~ l1_struct_0(X1) ),
% 7.79/1.44      inference(cnf_transformation,[],[f83]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_3374,plain,
% 7.79/1.44      ( r1_tsep_1(X0,X1) != iProver_top
% 7.79/1.44      | r1_tsep_1(X1,X0) = iProver_top
% 7.79/1.44      | l1_struct_0(X0) != iProver_top
% 7.79/1.44      | l1_struct_0(X1) != iProver_top ),
% 7.79/1.44      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_4929,plain,
% 7.79/1.44      ( r1_tsep_1(sK8,sK7) = iProver_top
% 7.79/1.44      | l1_struct_0(sK7) != iProver_top
% 7.79/1.44      | l1_struct_0(sK8) != iProver_top ),
% 7.79/1.44      inference(superposition,[status(thm)],[c_3373,c_3374]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_33,negated_conjecture,
% 7.79/1.44      ( ~ r1_tsep_1(sK6,sK8) | ~ r1_tsep_1(sK8,sK6) ),
% 7.79/1.44      inference(cnf_transformation,[],[f93]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_3372,plain,
% 7.79/1.44      ( r1_tsep_1(sK6,sK8) != iProver_top
% 7.79/1.44      | r1_tsep_1(sK8,sK6) != iProver_top ),
% 7.79/1.44      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_35,negated_conjecture,
% 7.79/1.44      ( m1_pre_topc(sK8,sK5) ),
% 7.79/1.44      inference(cnf_transformation,[],[f91]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_50,plain,
% 7.79/1.44      ( m1_pre_topc(sK8,sK5) = iProver_top ),
% 7.79/1.44      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_52,plain,
% 7.79/1.44      ( r1_tsep_1(sK6,sK8) != iProver_top
% 7.79/1.44      | r1_tsep_1(sK8,sK6) != iProver_top ),
% 7.79/1.44      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_77,plain,
% 7.79/1.44      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 7.79/1.44      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_79,plain,
% 7.79/1.44      ( l1_pre_topc(sK8) != iProver_top
% 7.79/1.44      | l1_struct_0(sK8) = iProver_top ),
% 7.79/1.44      inference(instantiation,[status(thm)],[c_77]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_3456,plain,
% 7.79/1.44      ( r1_tsep_1(sK6,sK8)
% 7.79/1.44      | ~ r1_tsep_1(sK8,sK6)
% 7.79/1.44      | ~ l1_struct_0(sK6)
% 7.79/1.44      | ~ l1_struct_0(sK8) ),
% 7.79/1.44      inference(instantiation,[status(thm)],[c_31]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_3457,plain,
% 7.79/1.44      ( r1_tsep_1(sK6,sK8) = iProver_top
% 7.79/1.44      | r1_tsep_1(sK8,sK6) != iProver_top
% 7.79/1.44      | l1_struct_0(sK6) != iProver_top
% 7.79/1.44      | l1_struct_0(sK8) != iProver_top ),
% 7.79/1.44      inference(predicate_to_equality,[status(thm)],[c_3456]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_3583,plain,
% 7.79/1.44      ( ~ l1_pre_topc(sK6) | l1_struct_0(sK6) ),
% 7.79/1.44      inference(instantiation,[status(thm)],[c_22]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_3584,plain,
% 7.79/1.44      ( l1_pre_topc(sK6) != iProver_top
% 7.79/1.44      | l1_struct_0(sK6) = iProver_top ),
% 7.79/1.44      inference(predicate_to_equality,[status(thm)],[c_3583]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_3672,plain,
% 7.79/1.44      ( m1_pre_topc(X0,sK5) != iProver_top
% 7.79/1.44      | l1_pre_topc(X0) = iProver_top
% 7.79/1.44      | l1_pre_topc(sK5) != iProver_top ),
% 7.79/1.44      inference(predicate_to_equality,[status(thm)],[c_3671]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_3674,plain,
% 7.79/1.44      ( m1_pre_topc(sK8,sK5) != iProver_top
% 7.79/1.44      | l1_pre_topc(sK5) != iProver_top
% 7.79/1.44      | l1_pre_topc(sK8) = iProver_top ),
% 7.79/1.44      inference(instantiation,[status(thm)],[c_3672]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(c_3802,plain,
% 7.79/1.44      ( r1_tsep_1(sK8,sK6) != iProver_top ),
% 7.79/1.44      inference(global_propositional_subsumption,
% 7.79/1.44                [status(thm)],
% 7.79/1.44                [c_3372,c_44,c_46,c_50,c_52,c_79,c_3457,c_3584,c_3674,
% 7.79/1.44                 c_3753]) ).
% 7.79/1.44  
% 7.79/1.44  cnf(contradiction,plain,
% 7.79/1.44      ( $false ),
% 7.79/1.44      inference(minisat,
% 7.79/1.44                [status(thm)],
% 7.79/1.44                [c_28003,c_7880,c_4929,c_4590,c_3802,c_3753,c_3674,
% 7.79/1.44                 c_3584,c_79,c_50,c_46,c_44]) ).
% 7.79/1.44  
% 7.79/1.44  
% 7.79/1.44  % SZS output end CNFRefutation for theBenchmark.p
% 7.79/1.44  
% 7.79/1.44  ------                               Statistics
% 7.79/1.44  
% 7.79/1.44  ------ General
% 7.79/1.44  
% 7.79/1.44  abstr_ref_over_cycles:                  0
% 7.79/1.44  abstr_ref_under_cycles:                 0
% 7.79/1.44  gc_basic_clause_elim:                   0
% 7.79/1.44  forced_gc_time:                         0
% 7.79/1.44  parsing_time:                           0.013
% 7.79/1.44  unif_index_cands_time:                  0.
% 7.79/1.44  unif_index_add_time:                    0.
% 7.79/1.44  orderings_time:                         0.
% 7.79/1.44  out_proof_time:                         0.014
% 7.79/1.44  total_time:                             0.988
% 7.79/1.44  num_of_symbols:                         57
% 7.79/1.44  num_of_terms:                           35554
% 7.79/1.44  
% 7.79/1.44  ------ Preprocessing
% 7.79/1.44  
% 7.79/1.44  num_of_splits:                          0
% 7.79/1.44  num_of_split_atoms:                     0
% 7.79/1.44  num_of_reused_defs:                     0
% 7.79/1.44  num_eq_ax_congr_red:                    47
% 7.79/1.44  num_of_sem_filtered_clauses:            1
% 7.79/1.44  num_of_subtypes:                        0
% 7.79/1.44  monotx_restored_types:                  0
% 7.79/1.44  sat_num_of_epr_types:                   0
% 7.79/1.44  sat_num_of_non_cyclic_types:            0
% 7.79/1.44  sat_guarded_non_collapsed_types:        0
% 7.79/1.44  num_pure_diseq_elim:                    0
% 7.79/1.44  simp_replaced_by:                       0
% 7.79/1.44  res_preprocessed:                       196
% 7.79/1.44  prep_upred:                             0
% 7.79/1.44  prep_unflattend:                        102
% 7.79/1.44  smt_new_axioms:                         0
% 7.79/1.44  pred_elim_cands:                        11
% 7.79/1.44  pred_elim:                              1
% 7.79/1.44  pred_elim_cl:                           1
% 7.79/1.44  pred_elim_cycles:                       5
% 7.79/1.44  merged_defs:                            0
% 7.79/1.44  merged_defs_ncl:                        0
% 7.79/1.44  bin_hyper_res:                          0
% 7.79/1.44  prep_cycles:                            4
% 7.79/1.44  pred_elim_time:                         0.045
% 7.79/1.44  splitting_time:                         0.
% 7.79/1.44  sem_filter_time:                        0.
% 7.79/1.44  monotx_time:                            0.001
% 7.79/1.44  subtype_inf_time:                       0.
% 7.79/1.44  
% 7.79/1.44  ------ Problem properties
% 7.79/1.44  
% 7.79/1.44  clauses:                                41
% 7.79/1.44  conjectures:                            11
% 7.79/1.44  epr:                                    18
% 7.79/1.44  horn:                                   31
% 7.79/1.44  ground:                                 11
% 7.79/1.44  unary:                                  11
% 7.79/1.44  binary:                                 7
% 7.79/1.44  lits:                                   133
% 7.79/1.44  lits_eq:                                8
% 7.79/1.44  fd_pure:                                0
% 7.79/1.44  fd_pseudo:                              0
% 7.79/1.44  fd_cond:                                0
% 7.79/1.44  fd_pseudo_cond:                         2
% 7.79/1.44  ac_symbols:                             0
% 7.79/1.44  
% 7.79/1.44  ------ Propositional Solver
% 7.79/1.44  
% 7.79/1.44  prop_solver_calls:                      32
% 7.79/1.44  prop_fast_solver_calls:                 3010
% 7.79/1.44  smt_solver_calls:                       0
% 7.79/1.44  smt_fast_solver_calls:                  0
% 7.79/1.44  prop_num_of_clauses:                    10309
% 7.79/1.44  prop_preprocess_simplified:             19826
% 7.79/1.44  prop_fo_subsumed:                       117
% 7.79/1.44  prop_solver_time:                       0.
% 7.79/1.44  smt_solver_time:                        0.
% 7.79/1.44  smt_fast_solver_time:                   0.
% 7.79/1.44  prop_fast_solver_time:                  0.
% 7.79/1.44  prop_unsat_core_time:                   0.001
% 7.79/1.44  
% 7.79/1.44  ------ QBF
% 7.79/1.44  
% 7.79/1.44  qbf_q_res:                              0
% 7.79/1.44  qbf_num_tautologies:                    0
% 7.79/1.44  qbf_prep_cycles:                        0
% 7.79/1.44  
% 7.79/1.44  ------ BMC1
% 7.79/1.44  
% 7.79/1.44  bmc1_current_bound:                     -1
% 7.79/1.44  bmc1_last_solved_bound:                 -1
% 7.79/1.44  bmc1_unsat_core_size:                   -1
% 7.79/1.44  bmc1_unsat_core_parents_size:           -1
% 7.79/1.44  bmc1_merge_next_fun:                    0
% 7.79/1.44  bmc1_unsat_core_clauses_time:           0.
% 7.79/1.44  
% 7.79/1.44  ------ Instantiation
% 7.79/1.44  
% 7.79/1.44  inst_num_of_clauses:                    2311
% 7.79/1.44  inst_num_in_passive:                    226
% 7.79/1.44  inst_num_in_active:                     1670
% 7.79/1.44  inst_num_in_unprocessed:                415
% 7.79/1.44  inst_num_of_loops:                      1860
% 7.79/1.44  inst_num_of_learning_restarts:          0
% 7.79/1.44  inst_num_moves_active_passive:          187
% 7.79/1.44  inst_lit_activity:                      0
% 7.79/1.44  inst_lit_activity_moves:                1
% 7.79/1.44  inst_num_tautologies:                   0
% 7.79/1.44  inst_num_prop_implied:                  0
% 7.79/1.44  inst_num_existing_simplified:           0
% 7.79/1.44  inst_num_eq_res_simplified:             0
% 7.79/1.44  inst_num_child_elim:                    0
% 7.79/1.44  inst_num_of_dismatching_blockings:      6186
% 7.79/1.44  inst_num_of_non_proper_insts:           3610
% 7.79/1.44  inst_num_of_duplicates:                 0
% 7.79/1.44  inst_inst_num_from_inst_to_res:         0
% 7.79/1.44  inst_dismatching_checking_time:         0.
% 7.79/1.44  
% 7.79/1.44  ------ Resolution
% 7.79/1.44  
% 7.79/1.44  res_num_of_clauses:                     0
% 7.79/1.44  res_num_in_passive:                     0
% 7.79/1.44  res_num_in_active:                      0
% 7.79/1.44  res_num_of_loops:                       200
% 7.79/1.44  res_forward_subset_subsumed:            158
% 7.79/1.44  res_backward_subset_subsumed:           0
% 7.79/1.44  res_forward_subsumed:                   0
% 7.79/1.44  res_backward_subsumed:                  0
% 7.79/1.44  res_forward_subsumption_resolution:     2
% 7.79/1.44  res_backward_subsumption_resolution:    0
% 7.79/1.44  res_clause_to_clause_subsumption:       4948
% 7.79/1.44  res_orphan_elimination:                 0
% 7.79/1.44  res_tautology_del:                      67
% 7.79/1.44  res_num_eq_res_simplified:              0
% 7.79/1.44  res_num_sel_changes:                    0
% 7.79/1.44  res_moves_from_active_to_pass:          0
% 7.79/1.44  
% 7.79/1.44  ------ Superposition
% 7.79/1.44  
% 7.79/1.44  sup_time_total:                         0.
% 7.79/1.44  sup_time_generating:                    0.
% 7.79/1.44  sup_time_sim_full:                      0.
% 7.79/1.44  sup_time_sim_immed:                     0.
% 7.79/1.44  
% 7.79/1.44  sup_num_of_clauses:                     1181
% 7.79/1.44  sup_num_in_active:                      347
% 7.79/1.44  sup_num_in_passive:                     834
% 7.79/1.44  sup_num_of_loops:                       371
% 7.79/1.44  sup_fw_superposition:                   866
% 7.79/1.44  sup_bw_superposition:                   1140
% 7.79/1.44  sup_immediate_simplified:               775
% 7.79/1.44  sup_given_eliminated:                   0
% 7.79/1.44  comparisons_done:                       0
% 7.79/1.44  comparisons_avoided:                    0
% 7.79/1.44  
% 7.79/1.44  ------ Simplifications
% 7.79/1.44  
% 7.79/1.44  
% 7.79/1.44  sim_fw_subset_subsumed:                 53
% 7.79/1.44  sim_bw_subset_subsumed:                 6
% 7.79/1.44  sim_fw_subsumed:                        189
% 7.79/1.44  sim_bw_subsumed:                        10
% 7.79/1.44  sim_fw_subsumption_res:                 0
% 7.79/1.44  sim_bw_subsumption_res:                 0
% 7.79/1.44  sim_tautology_del:                      220
% 7.79/1.44  sim_eq_tautology_del:                   129
% 7.79/1.44  sim_eq_res_simp:                        1
% 7.79/1.44  sim_fw_demodulated:                     381
% 7.79/1.44  sim_bw_demodulated:                     23
% 7.79/1.44  sim_light_normalised:                   361
% 7.79/1.44  sim_joinable_taut:                      0
% 7.79/1.44  sim_joinable_simp:                      0
% 7.79/1.44  sim_ac_normalised:                      0
% 7.79/1.44  sim_smt_subsumption:                    0
% 7.79/1.44  
%------------------------------------------------------------------------------
