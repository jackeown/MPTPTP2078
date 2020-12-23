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
% DateTime   : Thu Dec  3 12:22:08 EST 2020

% Result     : Theorem 39.13s
% Output     : CNFRefutation 39.13s
% Verified   : 
% Statistics : Number of formulae       :  194 (1396 expanded)
%              Number of clauses        :  131 ( 442 expanded)
%              Number of leaves         :   17 ( 436 expanded)
%              Depth                    :   24
%              Number of atoms          :  840 (11586 expanded)
%              Number of equality atoms :  256 ( 598 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
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
                 => ( ( m1_pre_topc(X3,X2)
                      & m1_pre_topc(X1,X2) )
                   => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                   => ( ( m1_pre_topc(X3,X2)
                        & m1_pre_topc(X1,X2) )
                     => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
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
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
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
    inference(flattening,[],[f20])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
          & m1_pre_topc(X3,X2)
          & m1_pre_topc(X1,X2)
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ~ m1_pre_topc(k1_tsep_1(X0,X1,sK8),X2)
        & m1_pre_topc(sK8,X2)
        & m1_pre_topc(X1,X2)
        & m1_pre_topc(sK8,X0)
        & ~ v2_struct_0(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
              & m1_pre_topc(X3,X2)
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),sK7)
            & m1_pre_topc(X3,sK7)
            & m1_pre_topc(X1,sK7)
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK7,X0)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k1_tsep_1(X0,sK6,X3),X2)
                & m1_pre_topc(X3,X2)
                & m1_pre_topc(sK6,X2)
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                    & m1_pre_topc(X3,X2)
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
                  ( ~ m1_pre_topc(k1_tsep_1(sK5,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK5)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK5)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK5)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK5,sK6,sK8),sK7)
    & m1_pre_topc(sK8,sK7)
    & m1_pre_topc(sK6,sK7)
    & m1_pre_topc(sK8,sK5)
    & ~ v2_struct_0(sK8)
    & m1_pre_topc(sK7,sK5)
    & ~ v2_struct_0(sK7)
    & m1_pre_topc(sK6,sK5)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f21,f38,f37,f36,f35])).

fof(f73,plain,(
    m1_pre_topc(sK8,sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    m1_pre_topc(sK6,sK7) ),
    inference(cnf_transformation,[],[f39])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(flattening,[],[f16])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f65,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,(
    m1_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
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
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
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

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
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

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
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
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f39])).

fof(f22,plain,(
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

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f31,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f31,f30,f29])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f64,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK5,sK6,sK8),sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
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

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f11,f23,f22])).

fof(f53,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f41,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK8,sK7) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_324,negated_conjecture,
    ( m1_pre_topc(sK8,sK7) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_987,plain,
    ( m1_pre_topc(sK8,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_324])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK6,sK7) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_323,negated_conjecture,
    ( m1_pre_topc(sK6,sK7) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_988,plain,
    ( m1_pre_topc(sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_323])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_330,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ m1_pre_topc(X2_53,X1_53)
    | m1_pre_topc(k1_tsep_1(X1_53,X0_53,X2_53),X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | ~ l1_pre_topc(X1_53) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_981,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X2_53,X1_53) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1_53,X0_53,X2_53),X1_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_330])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_332,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_979,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_4142,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X2_53,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(k1_tsep_1(X1_53,X0_53,X2_53)) = iProver_top ),
    inference(superposition,[status(thm)],[c_981,c_979])).

cnf(c_14,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_333,plain,
    ( ~ l1_pre_topc(X0_53)
    | l1_struct_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_978,plain,
    ( l1_pre_topc(X0_53) != iProver_top
    | l1_struct_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_333])).

cnf(c_13551,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X2_53,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_struct_0(k1_tsep_1(X1_53,X0_53,X2_53)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4142,c_978])).

cnf(c_0,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_347,plain,
    ( ~ l1_struct_0(X0_53)
    | u1_struct_0(X0_53) = k2_struct_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_964,plain,
    ( u1_struct_0(X0_53) = k2_struct_0(X0_53)
    | l1_struct_0(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_347])).

cnf(c_15262,plain,
    ( u1_struct_0(k1_tsep_1(X0_53,X1_53,X2_53)) = k2_struct_0(k1_tsep_1(X0_53,X1_53,X2_53))
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_13551,c_964])).

cnf(c_17279,plain,
    ( u1_struct_0(k1_tsep_1(sK7,sK6,X0_53)) = k2_struct_0(k1_tsep_1(sK7,sK6,X0_53))
    | m1_pre_topc(X0_53,sK7) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_988,c_15262])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_37,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_38,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_40,plain,
    ( v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_320,negated_conjecture,
    ( m1_pre_topc(sK7,sK5) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1545,plain,
    ( l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[status(thm)],[c_332,c_320])).

cnf(c_1546,plain,
    ( l1_pre_topc(sK7) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1545])).

cnf(c_17558,plain,
    ( v2_struct_0(X0_53) = iProver_top
    | m1_pre_topc(X0_53,sK7) != iProver_top
    | u1_struct_0(k1_tsep_1(sK7,sK6,X0_53)) = k2_struct_0(k1_tsep_1(sK7,sK6,X0_53)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17279,c_37,c_38,c_40,c_1546])).

cnf(c_17559,plain,
    ( u1_struct_0(k1_tsep_1(sK7,sK6,X0_53)) = k2_struct_0(k1_tsep_1(sK7,sK6,X0_53))
    | m1_pre_topc(X0_53,sK7) != iProver_top
    | v2_struct_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_17558])).

cnf(c_17567,plain,
    ( u1_struct_0(k1_tsep_1(sK7,sK6,sK8)) = k2_struct_0(k1_tsep_1(sK7,sK6,sK8))
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_987,c_17559])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_322,negated_conjecture,
    ( m1_pre_topc(sK8,sK5) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_989,plain,
    ( m1_pre_topc(sK8,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_322])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_318,negated_conjecture,
    ( m1_pre_topc(sK6,sK5) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_993,plain,
    ( m1_pre_topc(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f76])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v1_pre_topc(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_289,plain,
    ( ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_20,c_19,c_18])).

cnf(c_290,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(renaming,[status(thm)],[c_289])).

cnf(c_313,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ m1_pre_topc(X2_53,X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | ~ l1_pre_topc(X1_53)
    | u1_struct_0(k1_tsep_1(X1_53,X0_53,X2_53)) = k2_xboole_0(u1_struct_0(X0_53),u1_struct_0(X2_53)) ),
    inference(subtyping,[status(esa)],[c_290])).

cnf(c_998,plain,
    ( u1_struct_0(k1_tsep_1(X0_53,X1_53,X2_53)) = k2_xboole_0(u1_struct_0(X1_53),u1_struct_0(X2_53))
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_5307,plain,
    ( k2_xboole_0(u1_struct_0(sK6),u1_struct_0(X0_53)) = u1_struct_0(k1_tsep_1(sK5,sK6,X0_53))
    | m1_pre_topc(X0_53,sK5) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_993,c_998])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_35,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_6209,plain,
    ( v2_struct_0(X0_53) = iProver_top
    | m1_pre_topc(X0_53,sK5) != iProver_top
    | k2_xboole_0(u1_struct_0(sK6),u1_struct_0(X0_53)) = u1_struct_0(k1_tsep_1(sK5,sK6,X0_53)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5307,c_35,c_37,c_38])).

cnf(c_6210,plain,
    ( k2_xboole_0(u1_struct_0(sK6),u1_struct_0(X0_53)) = u1_struct_0(k1_tsep_1(sK5,sK6,X0_53))
    | m1_pre_topc(X0_53,sK5) != iProver_top
    | v2_struct_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_6209])).

cnf(c_1962,plain,
    ( l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_988,c_979])).

cnf(c_1541,plain,
    ( ~ l1_pre_topc(sK7)
    | l1_pre_topc(sK6) ),
    inference(resolution,[status(thm)],[c_332,c_323])).

cnf(c_1542,plain,
    ( l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1541])).

cnf(c_2881,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1962,c_37,c_1542,c_1546])).

cnf(c_2886,plain,
    ( l1_struct_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2881,c_978])).

cnf(c_4133,plain,
    ( u1_struct_0(sK6) = k2_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_2886,c_964])).

cnf(c_6215,plain,
    ( k2_xboole_0(k2_struct_0(sK6),u1_struct_0(X0_53)) = u1_struct_0(k1_tsep_1(sK5,sK6,X0_53))
    | m1_pre_topc(X0_53,sK5) != iProver_top
    | v2_struct_0(X0_53) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6210,c_4133])).

cnf(c_6222,plain,
    ( k2_xboole_0(k2_struct_0(sK6),u1_struct_0(sK8)) = u1_struct_0(k1_tsep_1(sK5,sK6,sK8))
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_989,c_6215])).

cnf(c_1961,plain,
    ( l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_987,c_979])).

cnf(c_1543,plain,
    ( l1_pre_topc(sK8)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[status(thm)],[c_332,c_322])).

cnf(c_1544,plain,
    ( l1_pre_topc(sK8) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1543])).

cnf(c_2048,plain,
    ( l1_pre_topc(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1961,c_37,c_1544])).

cnf(c_2053,plain,
    ( l1_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2048,c_978])).

cnf(c_3967,plain,
    ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(superposition,[status(thm)],[c_2053,c_964])).

cnf(c_6254,plain,
    ( k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8)) = u1_struct_0(k1_tsep_1(sK5,sK6,sK8))
    | v2_struct_0(sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6222,c_3967])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_42,plain,
    ( v2_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8071,plain,
    ( k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8)) = u1_struct_0(k1_tsep_1(sK5,sK6,sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6254,c_42])).

cnf(c_5304,plain,
    ( k2_xboole_0(u1_struct_0(sK6),u1_struct_0(X0_53)) = u1_struct_0(k1_tsep_1(sK7,sK6,X0_53))
    | m1_pre_topc(X0_53,sK7) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_988,c_998])).

cnf(c_6009,plain,
    ( v2_struct_0(X0_53) = iProver_top
    | m1_pre_topc(X0_53,sK7) != iProver_top
    | k2_xboole_0(u1_struct_0(sK6),u1_struct_0(X0_53)) = u1_struct_0(k1_tsep_1(sK7,sK6,X0_53)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5304,c_37,c_38,c_40,c_1546])).

cnf(c_6010,plain,
    ( k2_xboole_0(u1_struct_0(sK6),u1_struct_0(X0_53)) = u1_struct_0(k1_tsep_1(sK7,sK6,X0_53))
    | m1_pre_topc(X0_53,sK7) != iProver_top
    | v2_struct_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_6009])).

cnf(c_6015,plain,
    ( k2_xboole_0(k2_struct_0(sK6),u1_struct_0(X0_53)) = u1_struct_0(k1_tsep_1(sK7,sK6,X0_53))
    | m1_pre_topc(X0_53,sK7) != iProver_top
    | v2_struct_0(X0_53) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6010,c_4133])).

cnf(c_6022,plain,
    ( k2_xboole_0(k2_struct_0(sK6),u1_struct_0(sK8)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK8))
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_987,c_6015])).

cnf(c_6048,plain,
    ( k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK8))
    | v2_struct_0(sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6022,c_3967])).

cnf(c_7254,plain,
    ( k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6048,c_42])).

cnf(c_8074,plain,
    ( u1_struct_0(k1_tsep_1(sK7,sK6,sK8)) = u1_struct_0(k1_tsep_1(sK5,sK6,sK8)) ),
    inference(demodulation,[status(thm)],[c_8071,c_7254])).

cnf(c_17593,plain,
    ( u1_struct_0(k1_tsep_1(sK5,sK6,sK8)) = k2_struct_0(k1_tsep_1(sK7,sK6,sK8))
    | v2_struct_0(sK8) = iProver_top ),
    inference(demodulation,[status(thm)],[c_17567,c_8074])).

cnf(c_90357,plain,
    ( u1_struct_0(k1_tsep_1(sK5,sK6,sK8)) = k2_struct_0(k1_tsep_1(sK7,sK6,sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17593,c_42])).

cnf(c_17282,plain,
    ( u1_struct_0(k1_tsep_1(sK5,sK6,X0_53)) = k2_struct_0(k1_tsep_1(sK5,sK6,X0_53))
    | m1_pre_topc(X0_53,sK5) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_993,c_15262])).

cnf(c_21694,plain,
    ( v2_struct_0(X0_53) = iProver_top
    | m1_pre_topc(X0_53,sK5) != iProver_top
    | u1_struct_0(k1_tsep_1(sK5,sK6,X0_53)) = k2_struct_0(k1_tsep_1(sK5,sK6,X0_53)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17282,c_35,c_37,c_38])).

cnf(c_21695,plain,
    ( u1_struct_0(k1_tsep_1(sK5,sK6,X0_53)) = k2_struct_0(k1_tsep_1(sK5,sK6,X0_53))
    | m1_pre_topc(X0_53,sK5) != iProver_top
    | v2_struct_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_21694])).

cnf(c_21703,plain,
    ( u1_struct_0(k1_tsep_1(sK5,sK6,sK8)) = k2_struct_0(k1_tsep_1(sK5,sK6,sK8))
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_989,c_21695])).

cnf(c_21844,plain,
    ( u1_struct_0(k1_tsep_1(sK5,sK6,sK8)) = k2_struct_0(k1_tsep_1(sK5,sK6,sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21703,c_42])).

cnf(c_90359,plain,
    ( k2_struct_0(k1_tsep_1(sK5,sK6,sK8)) = k2_struct_0(k1_tsep_1(sK7,sK6,sK8)) ),
    inference(light_normalisation,[status(thm)],[c_90357,c_21844])).

cnf(c_12,plain,
    ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
    | ~ sP0(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_335,plain,
    ( r1_tarski(k2_struct_0(X0_53),k2_struct_0(X1_53))
    | ~ sP0(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_976,plain,
    ( r1_tarski(k2_struct_0(X0_53),k2_struct_0(X1_53)) = iProver_top
    | sP0(X0_53,X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_335])).

cnf(c_90366,plain,
    ( r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK8)),k2_struct_0(X0_53)) = iProver_top
    | sP0(k1_tsep_1(sK7,sK6,sK8),X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_90359,c_976])).

cnf(c_991,plain,
    ( m1_pre_topc(sK7,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_320])).

cnf(c_1964,plain,
    ( l1_pre_topc(sK7) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_991,c_979])).

cnf(c_2889,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1964,c_37,c_1546])).

cnf(c_2894,plain,
    ( l1_struct_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2889,c_978])).

cnf(c_4712,plain,
    ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
    inference(superposition,[status(thm)],[c_2894,c_964])).

cnf(c_22,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_326,plain,
    ( ~ r1_tarski(u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ m1_pre_topc(X1_53,X2_53)
    | m1_pre_topc(X0_53,X1_53)
    | ~ v2_pre_topc(X2_53)
    | ~ l1_pre_topc(X2_53) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_985,plain,
    ( r1_tarski(u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X2_53) != iProver_top
    | m1_pre_topc(X0_53,X1_53) = iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_326])).

cnf(c_5785,plain,
    ( r1_tarski(u1_struct_0(X0_53),k2_struct_0(sK7)) != iProver_top
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK7) = iProver_top
    | m1_pre_topc(sK7,X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_4712,c_985])).

cnf(c_21900,plain,
    ( r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK8)),k2_struct_0(sK7)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK5,sK6,sK8),X0_53) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK5,sK6,sK8),sK7) = iProver_top
    | m1_pre_topc(sK7,X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_21844,c_5785])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_36,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_39,plain,
    ( m1_pre_topc(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_41,plain,
    ( m1_pre_topc(sK7,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_43,plain,
    ( m1_pre_topc(sK8,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(sK5,sK6,sK8),sK7) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_46,plain,
    ( m1_pre_topc(k1_tsep_1(sK5,sK6,sK8),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1459,plain,
    ( ~ m1_pre_topc(X0_53,sK5)
    | m1_pre_topc(k1_tsep_1(sK5,X0_53,sK8),sK5)
    | ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(X0_53)
    | v2_struct_0(sK8)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_330])).

cnf(c_1895,plain,
    ( m1_pre_topc(k1_tsep_1(sK5,sK6,sK8),sK5)
    | ~ m1_pre_topc(sK8,sK5)
    | ~ m1_pre_topc(sK6,sK5)
    | v2_struct_0(sK8)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_1896,plain,
    ( m1_pre_topc(k1_tsep_1(sK5,sK6,sK8),sK5) = iProver_top
    | m1_pre_topc(sK8,sK5) != iProver_top
    | m1_pre_topc(sK6,sK5) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1895])).

cnf(c_22268,plain,
    ( r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK8)),k2_struct_0(sK7)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK5,sK6,sK8),sK7) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK5,sK6,sK8),sK5) != iProver_top
    | m1_pre_topc(sK7,sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_21900])).

cnf(c_58207,plain,
    ( r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK8)),k2_struct_0(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21900,c_35,c_36,c_37,c_38,c_39,c_41,c_42,c_43,c_46,c_1896,c_22268])).

cnf(c_101939,plain,
    ( sP0(k1_tsep_1(sK7,sK6,sK8),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_90366,c_58207])).

cnf(c_8394,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK7,sK6,sK8),X0_53)
    | ~ l1_pre_topc(X0_53)
    | l1_pre_topc(k1_tsep_1(sK7,sK6,sK8)) ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_54145,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK7,sK6,sK8),sK7)
    | l1_pre_topc(k1_tsep_1(sK7,sK6,sK8))
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_8394])).

cnf(c_54146,plain,
    ( m1_pre_topc(k1_tsep_1(sK7,sK6,sK8),sK7) != iProver_top
    | l1_pre_topc(k1_tsep_1(sK7,sK6,sK8)) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54145])).

cnf(c_13,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_334,plain,
    ( sP1(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_3609,plain,
    ( sP1(sK7,k1_tsep_1(sK7,sK6,sK8))
    | ~ l1_pre_topc(k1_tsep_1(sK7,sK6,sK8))
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_3610,plain,
    ( sP1(sK7,k1_tsep_1(sK7,sK6,sK8)) = iProver_top
    | l1_pre_topc(k1_tsep_1(sK7,sK6,sK8)) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3609])).

cnf(c_2,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_345,plain,
    ( ~ sP1(X0_53,X1_53)
    | sP0(X1_53,X0_53)
    | ~ m1_pre_topc(X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2262,plain,
    ( ~ sP1(sK7,k1_tsep_1(sK7,sK6,sK8))
    | sP0(k1_tsep_1(sK7,sK6,sK8),sK7)
    | ~ m1_pre_topc(k1_tsep_1(sK7,sK6,sK8),sK7) ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_2263,plain,
    ( sP1(sK7,k1_tsep_1(sK7,sK6,sK8)) != iProver_top
    | sP0(k1_tsep_1(sK7,sK6,sK8),sK7) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK7,sK6,sK8),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2262])).

cnf(c_1449,plain,
    ( ~ m1_pre_topc(X0_53,sK7)
    | m1_pre_topc(k1_tsep_1(sK7,X0_53,sK8),sK7)
    | ~ m1_pre_topc(sK8,sK7)
    | v2_struct_0(X0_53)
    | v2_struct_0(sK7)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_330])).

cnf(c_1860,plain,
    ( m1_pre_topc(k1_tsep_1(sK7,sK6,sK8),sK7)
    | ~ m1_pre_topc(sK8,sK7)
    | ~ m1_pre_topc(sK6,sK7)
    | v2_struct_0(sK7)
    | v2_struct_0(sK8)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_1449])).

cnf(c_1861,plain,
    ( m1_pre_topc(k1_tsep_1(sK7,sK6,sK8),sK7) = iProver_top
    | m1_pre_topc(sK8,sK7) != iProver_top
    | m1_pre_topc(sK6,sK7) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1860])).

cnf(c_45,plain,
    ( m1_pre_topc(sK8,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_44,plain,
    ( m1_pre_topc(sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_101939,c_54146,c_3610,c_2263,c_1861,c_1546,c_45,c_44,c_42,c_40,c_38,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 39.13/5.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.13/5.49  
% 39.13/5.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.13/5.49  
% 39.13/5.49  ------  iProver source info
% 39.13/5.49  
% 39.13/5.49  git: date: 2020-06-30 10:37:57 +0100
% 39.13/5.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.13/5.49  git: non_committed_changes: false
% 39.13/5.49  git: last_make_outside_of_git: false
% 39.13/5.49  
% 39.13/5.49  ------ 
% 39.13/5.49  ------ Parsing...
% 39.13/5.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.13/5.49  
% 39.13/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 39.13/5.49  
% 39.13/5.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.13/5.49  
% 39.13/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.13/5.49  ------ Proving...
% 39.13/5.49  ------ Problem Properties 
% 39.13/5.49  
% 39.13/5.49  
% 39.13/5.49  clauses                                 35
% 39.13/5.49  conjectures                             12
% 39.13/5.49  EPR                                     16
% 39.13/5.49  Horn                                    26
% 39.13/5.49  unary                                   12
% 39.13/5.49  binary                                  3
% 39.13/5.49  lits                                    119
% 39.13/5.49  lits eq                                 7
% 39.13/5.49  fd_pure                                 0
% 39.13/5.49  fd_pseudo                               0
% 39.13/5.49  fd_cond                                 0
% 39.13/5.49  fd_pseudo_cond                          1
% 39.13/5.49  AC symbols                              0
% 39.13/5.49  
% 39.13/5.49  ------ Input Options Time Limit: Unbounded
% 39.13/5.49  
% 39.13/5.49  
% 39.13/5.49  ------ 
% 39.13/5.49  Current options:
% 39.13/5.49  ------ 
% 39.13/5.49  
% 39.13/5.49  
% 39.13/5.49  
% 39.13/5.49  
% 39.13/5.49  ------ Proving...
% 39.13/5.49  
% 39.13/5.49  
% 39.13/5.49  % SZS status Theorem for theBenchmark.p
% 39.13/5.49  
% 39.13/5.49  % SZS output start CNFRefutation for theBenchmark.p
% 39.13/5.49  
% 39.13/5.49  fof(f8,conjecture,(
% 39.13/5.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 39.13/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.13/5.49  
% 39.13/5.49  fof(f9,negated_conjecture,(
% 39.13/5.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 39.13/5.49    inference(negated_conjecture,[],[f8])).
% 39.13/5.49  
% 39.13/5.49  fof(f20,plain,(
% 39.13/5.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 39.13/5.49    inference(ennf_transformation,[],[f9])).
% 39.13/5.49  
% 39.13/5.49  fof(f21,plain,(
% 39.13/5.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 39.13/5.49    inference(flattening,[],[f20])).
% 39.13/5.49  
% 39.13/5.49  fof(f38,plain,(
% 39.13/5.49    ( ! [X2,X0,X1] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(X0,X1,sK8),X2) & m1_pre_topc(sK8,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(sK8,X0) & ~v2_struct_0(sK8))) )),
% 39.13/5.49    introduced(choice_axiom,[])).
% 39.13/5.49  
% 39.13/5.49  fof(f37,plain,(
% 39.13/5.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),sK7) & m1_pre_topc(X3,sK7) & m1_pre_topc(X1,sK7) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK7,X0) & ~v2_struct_0(sK7))) )),
% 39.13/5.49    introduced(choice_axiom,[])).
% 39.13/5.49  
% 39.13/5.49  fof(f36,plain,(
% 39.13/5.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,sK6,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK6,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 39.13/5.49    introduced(choice_axiom,[])).
% 39.13/5.49  
% 39.13/5.49  fof(f35,plain,(
% 39.13/5.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK5,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK5) & ~v2_struct_0(X1)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 39.13/5.49    introduced(choice_axiom,[])).
% 39.13/5.49  
% 39.13/5.49  fof(f39,plain,(
% 39.13/5.49    (((~m1_pre_topc(k1_tsep_1(sK5,sK6,sK8),sK7) & m1_pre_topc(sK8,sK7) & m1_pre_topc(sK6,sK7) & m1_pre_topc(sK8,sK5) & ~v2_struct_0(sK8)) & m1_pre_topc(sK7,sK5) & ~v2_struct_0(sK7)) & m1_pre_topc(sK6,sK5) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 39.13/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f21,f38,f37,f36,f35])).
% 39.13/5.49  
% 39.13/5.49  fof(f73,plain,(
% 39.13/5.49    m1_pre_topc(sK8,sK7)),
% 39.13/5.49    inference(cnf_transformation,[],[f39])).
% 39.13/5.49  
% 39.13/5.49  fof(f72,plain,(
% 39.13/5.49    m1_pre_topc(sK6,sK7)),
% 39.13/5.49    inference(cnf_transformation,[],[f39])).
% 39.13/5.49  
% 39.13/5.49  fof(f6,axiom,(
% 39.13/5.49    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 39.13/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.13/5.49  
% 39.13/5.49  fof(f16,plain,(
% 39.13/5.49    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 39.13/5.49    inference(ennf_transformation,[],[f6])).
% 39.13/5.49  
% 39.13/5.49  fof(f17,plain,(
% 39.13/5.49    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 39.13/5.49    inference(flattening,[],[f16])).
% 39.13/5.49  
% 39.13/5.49  fof(f60,plain,(
% 39.13/5.49    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.13/5.49    inference(cnf_transformation,[],[f17])).
% 39.13/5.49  
% 39.13/5.49  fof(f4,axiom,(
% 39.13/5.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 39.13/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.13/5.49  
% 39.13/5.49  fof(f13,plain,(
% 39.13/5.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 39.13/5.49    inference(ennf_transformation,[],[f4])).
% 39.13/5.49  
% 39.13/5.49  fof(f55,plain,(
% 39.13/5.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 39.13/5.49    inference(cnf_transformation,[],[f13])).
% 39.13/5.49  
% 39.13/5.49  fof(f3,axiom,(
% 39.13/5.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 39.13/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.13/5.49  
% 39.13/5.49  fof(f12,plain,(
% 39.13/5.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 39.13/5.49    inference(ennf_transformation,[],[f3])).
% 39.13/5.49  
% 39.13/5.49  fof(f54,plain,(
% 39.13/5.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 39.13/5.49    inference(cnf_transformation,[],[f12])).
% 39.13/5.49  
% 39.13/5.49  fof(f1,axiom,(
% 39.13/5.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 39.13/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.13/5.49  
% 39.13/5.49  fof(f10,plain,(
% 39.13/5.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 39.13/5.49    inference(ennf_transformation,[],[f1])).
% 39.13/5.49  
% 39.13/5.49  fof(f40,plain,(
% 39.13/5.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 39.13/5.49    inference(cnf_transformation,[],[f10])).
% 39.13/5.49  
% 39.13/5.49  fof(f65,plain,(
% 39.13/5.49    l1_pre_topc(sK5)),
% 39.13/5.49    inference(cnf_transformation,[],[f39])).
% 39.13/5.49  
% 39.13/5.49  fof(f66,plain,(
% 39.13/5.49    ~v2_struct_0(sK6)),
% 39.13/5.49    inference(cnf_transformation,[],[f39])).
% 39.13/5.49  
% 39.13/5.49  fof(f68,plain,(
% 39.13/5.49    ~v2_struct_0(sK7)),
% 39.13/5.49    inference(cnf_transformation,[],[f39])).
% 39.13/5.49  
% 39.13/5.49  fof(f69,plain,(
% 39.13/5.49    m1_pre_topc(sK7,sK5)),
% 39.13/5.49    inference(cnf_transformation,[],[f39])).
% 39.13/5.49  
% 39.13/5.49  fof(f71,plain,(
% 39.13/5.49    m1_pre_topc(sK8,sK5)),
% 39.13/5.49    inference(cnf_transformation,[],[f39])).
% 39.13/5.49  
% 39.13/5.49  fof(f67,plain,(
% 39.13/5.49    m1_pre_topc(sK6,sK5)),
% 39.13/5.49    inference(cnf_transformation,[],[f39])).
% 39.13/5.49  
% 39.13/5.49  fof(f5,axiom,(
% 39.13/5.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 39.13/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.13/5.49  
% 39.13/5.49  fof(f14,plain,(
% 39.13/5.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 39.13/5.49    inference(ennf_transformation,[],[f5])).
% 39.13/5.49  
% 39.13/5.49  fof(f15,plain,(
% 39.13/5.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 39.13/5.49    inference(flattening,[],[f14])).
% 39.13/5.49  
% 39.13/5.49  fof(f33,plain,(
% 39.13/5.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 39.13/5.49    inference(nnf_transformation,[],[f15])).
% 39.13/5.49  
% 39.13/5.49  fof(f56,plain,(
% 39.13/5.49    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.13/5.49    inference(cnf_transformation,[],[f33])).
% 39.13/5.49  
% 39.13/5.49  fof(f76,plain,(
% 39.13/5.49    ( ! [X2,X0,X1] : (u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.13/5.49    inference(equality_resolution,[],[f56])).
% 39.13/5.49  
% 39.13/5.49  fof(f58,plain,(
% 39.13/5.49    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.13/5.49    inference(cnf_transformation,[],[f17])).
% 39.13/5.49  
% 39.13/5.49  fof(f59,plain,(
% 39.13/5.49    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.13/5.49    inference(cnf_transformation,[],[f17])).
% 39.13/5.49  
% 39.13/5.49  fof(f63,plain,(
% 39.13/5.49    ~v2_struct_0(sK5)),
% 39.13/5.49    inference(cnf_transformation,[],[f39])).
% 39.13/5.49  
% 39.13/5.49  fof(f70,plain,(
% 39.13/5.49    ~v2_struct_0(sK8)),
% 39.13/5.49    inference(cnf_transformation,[],[f39])).
% 39.13/5.49  
% 39.13/5.49  fof(f22,plain,(
% 39.13/5.49    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 39.13/5.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 39.13/5.49  
% 39.13/5.49  fof(f26,plain,(
% 39.13/5.49    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 39.13/5.49    inference(nnf_transformation,[],[f22])).
% 39.13/5.49  
% 39.13/5.49  fof(f27,plain,(
% 39.13/5.49    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 39.13/5.49    inference(flattening,[],[f26])).
% 39.13/5.49  
% 39.13/5.49  fof(f28,plain,(
% 39.13/5.49    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 39.13/5.49    inference(rectify,[],[f27])).
% 39.13/5.49  
% 39.13/5.49  fof(f31,plain,(
% 39.13/5.49    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 39.13/5.49    introduced(choice_axiom,[])).
% 39.13/5.49  
% 39.13/5.49  fof(f30,plain,(
% 39.13/5.49    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 39.13/5.49    introduced(choice_axiom,[])).
% 39.13/5.49  
% 39.13/5.49  fof(f29,plain,(
% 39.13/5.49    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 39.13/5.49    introduced(choice_axiom,[])).
% 39.13/5.49  
% 39.13/5.49  fof(f32,plain,(
% 39.13/5.49    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 39.13/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f31,f30,f29])).
% 39.13/5.49  
% 39.13/5.49  fof(f43,plain,(
% 39.13/5.49    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 39.13/5.49    inference(cnf_transformation,[],[f32])).
% 39.13/5.49  
% 39.13/5.49  fof(f7,axiom,(
% 39.13/5.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 39.13/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.13/5.49  
% 39.13/5.49  fof(f18,plain,(
% 39.13/5.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 39.13/5.49    inference(ennf_transformation,[],[f7])).
% 39.13/5.49  
% 39.13/5.49  fof(f19,plain,(
% 39.13/5.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 39.13/5.49    inference(flattening,[],[f18])).
% 39.13/5.49  
% 39.13/5.49  fof(f34,plain,(
% 39.13/5.49    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 39.13/5.49    inference(nnf_transformation,[],[f19])).
% 39.13/5.49  
% 39.13/5.49  fof(f61,plain,(
% 39.13/5.49    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 39.13/5.49    inference(cnf_transformation,[],[f34])).
% 39.13/5.49  
% 39.13/5.49  fof(f64,plain,(
% 39.13/5.49    v2_pre_topc(sK5)),
% 39.13/5.49    inference(cnf_transformation,[],[f39])).
% 39.13/5.49  
% 39.13/5.49  fof(f74,plain,(
% 39.13/5.49    ~m1_pre_topc(k1_tsep_1(sK5,sK6,sK8),sK7)),
% 39.13/5.49    inference(cnf_transformation,[],[f39])).
% 39.13/5.49  
% 39.13/5.49  fof(f2,axiom,(
% 39.13/5.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 39.13/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.13/5.49  
% 39.13/5.49  fof(f11,plain,(
% 39.13/5.49    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 39.13/5.49    inference(ennf_transformation,[],[f2])).
% 39.13/5.49  
% 39.13/5.49  fof(f23,plain,(
% 39.13/5.49    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 39.13/5.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 39.13/5.49  
% 39.13/5.49  fof(f24,plain,(
% 39.13/5.49    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 39.13/5.49    inference(definition_folding,[],[f11,f23,f22])).
% 39.13/5.49  
% 39.13/5.49  fof(f53,plain,(
% 39.13/5.49    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 39.13/5.49    inference(cnf_transformation,[],[f24])).
% 39.13/5.49  
% 39.13/5.49  fof(f25,plain,(
% 39.13/5.49    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 39.13/5.49    inference(nnf_transformation,[],[f23])).
% 39.13/5.49  
% 39.13/5.49  fof(f41,plain,(
% 39.13/5.49    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 39.13/5.49    inference(cnf_transformation,[],[f25])).
% 39.13/5.49  
% 39.13/5.49  cnf(c_24,negated_conjecture,
% 39.13/5.49      ( m1_pre_topc(sK8,sK7) ),
% 39.13/5.49      inference(cnf_transformation,[],[f73]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_324,negated_conjecture,
% 39.13/5.49      ( m1_pre_topc(sK8,sK7) ),
% 39.13/5.49      inference(subtyping,[status(esa)],[c_24]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_987,plain,
% 39.13/5.49      ( m1_pre_topc(sK8,sK7) = iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_324]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_25,negated_conjecture,
% 39.13/5.49      ( m1_pre_topc(sK6,sK7) ),
% 39.13/5.49      inference(cnf_transformation,[],[f72]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_323,negated_conjecture,
% 39.13/5.49      ( m1_pre_topc(sK6,sK7) ),
% 39.13/5.49      inference(subtyping,[status(esa)],[c_25]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_988,plain,
% 39.13/5.49      ( m1_pre_topc(sK6,sK7) = iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_323]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_18,plain,
% 39.13/5.49      ( ~ m1_pre_topc(X0,X1)
% 39.13/5.49      | ~ m1_pre_topc(X2,X1)
% 39.13/5.49      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 39.13/5.49      | v2_struct_0(X1)
% 39.13/5.49      | v2_struct_0(X0)
% 39.13/5.49      | v2_struct_0(X2)
% 39.13/5.49      | ~ l1_pre_topc(X1) ),
% 39.13/5.49      inference(cnf_transformation,[],[f60]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_330,plain,
% 39.13/5.49      ( ~ m1_pre_topc(X0_53,X1_53)
% 39.13/5.49      | ~ m1_pre_topc(X2_53,X1_53)
% 39.13/5.49      | m1_pre_topc(k1_tsep_1(X1_53,X0_53,X2_53),X1_53)
% 39.13/5.49      | v2_struct_0(X0_53)
% 39.13/5.49      | v2_struct_0(X1_53)
% 39.13/5.49      | v2_struct_0(X2_53)
% 39.13/5.49      | ~ l1_pre_topc(X1_53) ),
% 39.13/5.49      inference(subtyping,[status(esa)],[c_18]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_981,plain,
% 39.13/5.49      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 39.13/5.49      | m1_pre_topc(X2_53,X1_53) != iProver_top
% 39.13/5.49      | m1_pre_topc(k1_tsep_1(X1_53,X0_53,X2_53),X1_53) = iProver_top
% 39.13/5.49      | v2_struct_0(X1_53) = iProver_top
% 39.13/5.49      | v2_struct_0(X0_53) = iProver_top
% 39.13/5.49      | v2_struct_0(X2_53) = iProver_top
% 39.13/5.49      | l1_pre_topc(X1_53) != iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_330]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_15,plain,
% 39.13/5.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 39.13/5.49      inference(cnf_transformation,[],[f55]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_332,plain,
% 39.13/5.49      ( ~ m1_pre_topc(X0_53,X1_53)
% 39.13/5.49      | ~ l1_pre_topc(X1_53)
% 39.13/5.49      | l1_pre_topc(X0_53) ),
% 39.13/5.49      inference(subtyping,[status(esa)],[c_15]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_979,plain,
% 39.13/5.49      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 39.13/5.49      | l1_pre_topc(X1_53) != iProver_top
% 39.13/5.49      | l1_pre_topc(X0_53) = iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_4142,plain,
% 39.13/5.49      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 39.13/5.49      | m1_pre_topc(X2_53,X1_53) != iProver_top
% 39.13/5.49      | v2_struct_0(X1_53) = iProver_top
% 39.13/5.49      | v2_struct_0(X0_53) = iProver_top
% 39.13/5.49      | v2_struct_0(X2_53) = iProver_top
% 39.13/5.49      | l1_pre_topc(X1_53) != iProver_top
% 39.13/5.49      | l1_pre_topc(k1_tsep_1(X1_53,X0_53,X2_53)) = iProver_top ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_981,c_979]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_14,plain,
% 39.13/5.49      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 39.13/5.49      inference(cnf_transformation,[],[f54]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_333,plain,
% 39.13/5.49      ( ~ l1_pre_topc(X0_53) | l1_struct_0(X0_53) ),
% 39.13/5.49      inference(subtyping,[status(esa)],[c_14]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_978,plain,
% 39.13/5.49      ( l1_pre_topc(X0_53) != iProver_top
% 39.13/5.49      | l1_struct_0(X0_53) = iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_333]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_13551,plain,
% 39.13/5.49      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 39.13/5.49      | m1_pre_topc(X2_53,X1_53) != iProver_top
% 39.13/5.49      | v2_struct_0(X1_53) = iProver_top
% 39.13/5.49      | v2_struct_0(X0_53) = iProver_top
% 39.13/5.49      | v2_struct_0(X2_53) = iProver_top
% 39.13/5.49      | l1_pre_topc(X1_53) != iProver_top
% 39.13/5.49      | l1_struct_0(k1_tsep_1(X1_53,X0_53,X2_53)) = iProver_top ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_4142,c_978]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_0,plain,
% 39.13/5.49      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 39.13/5.49      inference(cnf_transformation,[],[f40]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_347,plain,
% 39.13/5.49      ( ~ l1_struct_0(X0_53) | u1_struct_0(X0_53) = k2_struct_0(X0_53) ),
% 39.13/5.49      inference(subtyping,[status(esa)],[c_0]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_964,plain,
% 39.13/5.49      ( u1_struct_0(X0_53) = k2_struct_0(X0_53)
% 39.13/5.49      | l1_struct_0(X0_53) != iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_347]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_15262,plain,
% 39.13/5.49      ( u1_struct_0(k1_tsep_1(X0_53,X1_53,X2_53)) = k2_struct_0(k1_tsep_1(X0_53,X1_53,X2_53))
% 39.13/5.49      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 39.13/5.49      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 39.13/5.49      | v2_struct_0(X0_53) = iProver_top
% 39.13/5.49      | v2_struct_0(X1_53) = iProver_top
% 39.13/5.49      | v2_struct_0(X2_53) = iProver_top
% 39.13/5.49      | l1_pre_topc(X0_53) != iProver_top ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_13551,c_964]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_17279,plain,
% 39.13/5.49      ( u1_struct_0(k1_tsep_1(sK7,sK6,X0_53)) = k2_struct_0(k1_tsep_1(sK7,sK6,X0_53))
% 39.13/5.49      | m1_pre_topc(X0_53,sK7) != iProver_top
% 39.13/5.49      | v2_struct_0(X0_53) = iProver_top
% 39.13/5.49      | v2_struct_0(sK7) = iProver_top
% 39.13/5.49      | v2_struct_0(sK6) = iProver_top
% 39.13/5.49      | l1_pre_topc(sK7) != iProver_top ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_988,c_15262]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_32,negated_conjecture,
% 39.13/5.49      ( l1_pre_topc(sK5) ),
% 39.13/5.49      inference(cnf_transformation,[],[f65]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_37,plain,
% 39.13/5.49      ( l1_pre_topc(sK5) = iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_31,negated_conjecture,
% 39.13/5.49      ( ~ v2_struct_0(sK6) ),
% 39.13/5.49      inference(cnf_transformation,[],[f66]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_38,plain,
% 39.13/5.49      ( v2_struct_0(sK6) != iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_29,negated_conjecture,
% 39.13/5.49      ( ~ v2_struct_0(sK7) ),
% 39.13/5.49      inference(cnf_transformation,[],[f68]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_40,plain,
% 39.13/5.49      ( v2_struct_0(sK7) != iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_28,negated_conjecture,
% 39.13/5.49      ( m1_pre_topc(sK7,sK5) ),
% 39.13/5.49      inference(cnf_transformation,[],[f69]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_320,negated_conjecture,
% 39.13/5.49      ( m1_pre_topc(sK7,sK5) ),
% 39.13/5.49      inference(subtyping,[status(esa)],[c_28]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_1545,plain,
% 39.13/5.49      ( l1_pre_topc(sK7) | ~ l1_pre_topc(sK5) ),
% 39.13/5.49      inference(resolution,[status(thm)],[c_332,c_320]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_1546,plain,
% 39.13/5.49      ( l1_pre_topc(sK7) = iProver_top
% 39.13/5.49      | l1_pre_topc(sK5) != iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_1545]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_17558,plain,
% 39.13/5.49      ( v2_struct_0(X0_53) = iProver_top
% 39.13/5.49      | m1_pre_topc(X0_53,sK7) != iProver_top
% 39.13/5.49      | u1_struct_0(k1_tsep_1(sK7,sK6,X0_53)) = k2_struct_0(k1_tsep_1(sK7,sK6,X0_53)) ),
% 39.13/5.49      inference(global_propositional_subsumption,
% 39.13/5.49                [status(thm)],
% 39.13/5.49                [c_17279,c_37,c_38,c_40,c_1546]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_17559,plain,
% 39.13/5.49      ( u1_struct_0(k1_tsep_1(sK7,sK6,X0_53)) = k2_struct_0(k1_tsep_1(sK7,sK6,X0_53))
% 39.13/5.49      | m1_pre_topc(X0_53,sK7) != iProver_top
% 39.13/5.49      | v2_struct_0(X0_53) = iProver_top ),
% 39.13/5.49      inference(renaming,[status(thm)],[c_17558]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_17567,plain,
% 39.13/5.49      ( u1_struct_0(k1_tsep_1(sK7,sK6,sK8)) = k2_struct_0(k1_tsep_1(sK7,sK6,sK8))
% 39.13/5.49      | v2_struct_0(sK8) = iProver_top ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_987,c_17559]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_26,negated_conjecture,
% 39.13/5.49      ( m1_pre_topc(sK8,sK5) ),
% 39.13/5.49      inference(cnf_transformation,[],[f71]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_322,negated_conjecture,
% 39.13/5.49      ( m1_pre_topc(sK8,sK5) ),
% 39.13/5.49      inference(subtyping,[status(esa)],[c_26]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_989,plain,
% 39.13/5.49      ( m1_pre_topc(sK8,sK5) = iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_322]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_30,negated_conjecture,
% 39.13/5.49      ( m1_pre_topc(sK6,sK5) ),
% 39.13/5.49      inference(cnf_transformation,[],[f67]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_318,negated_conjecture,
% 39.13/5.49      ( m1_pre_topc(sK6,sK5) ),
% 39.13/5.49      inference(subtyping,[status(esa)],[c_30]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_993,plain,
% 39.13/5.49      ( m1_pre_topc(sK6,sK5) = iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_17,plain,
% 39.13/5.49      ( ~ m1_pre_topc(X0,X1)
% 39.13/5.49      | ~ m1_pre_topc(X2,X1)
% 39.13/5.49      | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 39.13/5.49      | v2_struct_0(X1)
% 39.13/5.49      | v2_struct_0(X0)
% 39.13/5.49      | v2_struct_0(X2)
% 39.13/5.49      | v2_struct_0(k1_tsep_1(X1,X0,X2))
% 39.13/5.49      | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 39.13/5.49      | ~ l1_pre_topc(X1)
% 39.13/5.49      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 39.13/5.49      inference(cnf_transformation,[],[f76]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_20,plain,
% 39.13/5.49      ( ~ m1_pre_topc(X0,X1)
% 39.13/5.49      | ~ m1_pre_topc(X2,X1)
% 39.13/5.49      | v2_struct_0(X1)
% 39.13/5.49      | v2_struct_0(X0)
% 39.13/5.49      | v2_struct_0(X2)
% 39.13/5.49      | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
% 39.13/5.49      | ~ l1_pre_topc(X1) ),
% 39.13/5.49      inference(cnf_transformation,[],[f58]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_19,plain,
% 39.13/5.49      ( ~ m1_pre_topc(X0,X1)
% 39.13/5.49      | ~ m1_pre_topc(X2,X1)
% 39.13/5.49      | v2_struct_0(X1)
% 39.13/5.49      | v2_struct_0(X0)
% 39.13/5.49      | v2_struct_0(X2)
% 39.13/5.49      | v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 39.13/5.49      | ~ l1_pre_topc(X1) ),
% 39.13/5.49      inference(cnf_transformation,[],[f59]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_289,plain,
% 39.13/5.49      ( ~ m1_pre_topc(X2,X1)
% 39.13/5.49      | ~ m1_pre_topc(X0,X1)
% 39.13/5.49      | v2_struct_0(X1)
% 39.13/5.49      | v2_struct_0(X0)
% 39.13/5.49      | v2_struct_0(X2)
% 39.13/5.49      | ~ l1_pre_topc(X1)
% 39.13/5.49      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 39.13/5.49      inference(global_propositional_subsumption,
% 39.13/5.49                [status(thm)],
% 39.13/5.49                [c_17,c_20,c_19,c_18]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_290,plain,
% 39.13/5.49      ( ~ m1_pre_topc(X0,X1)
% 39.13/5.49      | ~ m1_pre_topc(X2,X1)
% 39.13/5.49      | v2_struct_0(X0)
% 39.13/5.49      | v2_struct_0(X1)
% 39.13/5.49      | v2_struct_0(X2)
% 39.13/5.49      | ~ l1_pre_topc(X1)
% 39.13/5.49      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 39.13/5.49      inference(renaming,[status(thm)],[c_289]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_313,plain,
% 39.13/5.49      ( ~ m1_pre_topc(X0_53,X1_53)
% 39.13/5.49      | ~ m1_pre_topc(X2_53,X1_53)
% 39.13/5.49      | v2_struct_0(X0_53)
% 39.13/5.49      | v2_struct_0(X1_53)
% 39.13/5.49      | v2_struct_0(X2_53)
% 39.13/5.49      | ~ l1_pre_topc(X1_53)
% 39.13/5.49      | u1_struct_0(k1_tsep_1(X1_53,X0_53,X2_53)) = k2_xboole_0(u1_struct_0(X0_53),u1_struct_0(X2_53)) ),
% 39.13/5.49      inference(subtyping,[status(esa)],[c_290]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_998,plain,
% 39.13/5.49      ( u1_struct_0(k1_tsep_1(X0_53,X1_53,X2_53)) = k2_xboole_0(u1_struct_0(X1_53),u1_struct_0(X2_53))
% 39.13/5.49      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 39.13/5.49      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 39.13/5.49      | v2_struct_0(X0_53) = iProver_top
% 39.13/5.49      | v2_struct_0(X1_53) = iProver_top
% 39.13/5.49      | v2_struct_0(X2_53) = iProver_top
% 39.13/5.49      | l1_pre_topc(X0_53) != iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_5307,plain,
% 39.13/5.49      ( k2_xboole_0(u1_struct_0(sK6),u1_struct_0(X0_53)) = u1_struct_0(k1_tsep_1(sK5,sK6,X0_53))
% 39.13/5.49      | m1_pre_topc(X0_53,sK5) != iProver_top
% 39.13/5.49      | v2_struct_0(X0_53) = iProver_top
% 39.13/5.49      | v2_struct_0(sK6) = iProver_top
% 39.13/5.49      | v2_struct_0(sK5) = iProver_top
% 39.13/5.49      | l1_pre_topc(sK5) != iProver_top ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_993,c_998]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_34,negated_conjecture,
% 39.13/5.49      ( ~ v2_struct_0(sK5) ),
% 39.13/5.49      inference(cnf_transformation,[],[f63]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_35,plain,
% 39.13/5.49      ( v2_struct_0(sK5) != iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_6209,plain,
% 39.13/5.49      ( v2_struct_0(X0_53) = iProver_top
% 39.13/5.49      | m1_pre_topc(X0_53,sK5) != iProver_top
% 39.13/5.49      | k2_xboole_0(u1_struct_0(sK6),u1_struct_0(X0_53)) = u1_struct_0(k1_tsep_1(sK5,sK6,X0_53)) ),
% 39.13/5.49      inference(global_propositional_subsumption,
% 39.13/5.49                [status(thm)],
% 39.13/5.49                [c_5307,c_35,c_37,c_38]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_6210,plain,
% 39.13/5.49      ( k2_xboole_0(u1_struct_0(sK6),u1_struct_0(X0_53)) = u1_struct_0(k1_tsep_1(sK5,sK6,X0_53))
% 39.13/5.49      | m1_pre_topc(X0_53,sK5) != iProver_top
% 39.13/5.49      | v2_struct_0(X0_53) = iProver_top ),
% 39.13/5.49      inference(renaming,[status(thm)],[c_6209]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_1962,plain,
% 39.13/5.49      ( l1_pre_topc(sK7) != iProver_top
% 39.13/5.49      | l1_pre_topc(sK6) = iProver_top ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_988,c_979]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_1541,plain,
% 39.13/5.49      ( ~ l1_pre_topc(sK7) | l1_pre_topc(sK6) ),
% 39.13/5.49      inference(resolution,[status(thm)],[c_332,c_323]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_1542,plain,
% 39.13/5.49      ( l1_pre_topc(sK7) != iProver_top
% 39.13/5.49      | l1_pre_topc(sK6) = iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_1541]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_2881,plain,
% 39.13/5.49      ( l1_pre_topc(sK6) = iProver_top ),
% 39.13/5.49      inference(global_propositional_subsumption,
% 39.13/5.49                [status(thm)],
% 39.13/5.49                [c_1962,c_37,c_1542,c_1546]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_2886,plain,
% 39.13/5.49      ( l1_struct_0(sK6) = iProver_top ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_2881,c_978]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_4133,plain,
% 39.13/5.49      ( u1_struct_0(sK6) = k2_struct_0(sK6) ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_2886,c_964]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_6215,plain,
% 39.13/5.49      ( k2_xboole_0(k2_struct_0(sK6),u1_struct_0(X0_53)) = u1_struct_0(k1_tsep_1(sK5,sK6,X0_53))
% 39.13/5.49      | m1_pre_topc(X0_53,sK5) != iProver_top
% 39.13/5.49      | v2_struct_0(X0_53) = iProver_top ),
% 39.13/5.49      inference(light_normalisation,[status(thm)],[c_6210,c_4133]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_6222,plain,
% 39.13/5.49      ( k2_xboole_0(k2_struct_0(sK6),u1_struct_0(sK8)) = u1_struct_0(k1_tsep_1(sK5,sK6,sK8))
% 39.13/5.49      | v2_struct_0(sK8) = iProver_top ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_989,c_6215]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_1961,plain,
% 39.13/5.49      ( l1_pre_topc(sK7) != iProver_top
% 39.13/5.49      | l1_pre_topc(sK8) = iProver_top ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_987,c_979]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_1543,plain,
% 39.13/5.49      ( l1_pre_topc(sK8) | ~ l1_pre_topc(sK5) ),
% 39.13/5.49      inference(resolution,[status(thm)],[c_332,c_322]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_1544,plain,
% 39.13/5.49      ( l1_pre_topc(sK8) = iProver_top
% 39.13/5.49      | l1_pre_topc(sK5) != iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_1543]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_2048,plain,
% 39.13/5.49      ( l1_pre_topc(sK8) = iProver_top ),
% 39.13/5.49      inference(global_propositional_subsumption,
% 39.13/5.49                [status(thm)],
% 39.13/5.49                [c_1961,c_37,c_1544]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_2053,plain,
% 39.13/5.49      ( l1_struct_0(sK8) = iProver_top ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_2048,c_978]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_3967,plain,
% 39.13/5.49      ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_2053,c_964]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_6254,plain,
% 39.13/5.49      ( k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8)) = u1_struct_0(k1_tsep_1(sK5,sK6,sK8))
% 39.13/5.49      | v2_struct_0(sK8) = iProver_top ),
% 39.13/5.49      inference(light_normalisation,[status(thm)],[c_6222,c_3967]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_27,negated_conjecture,
% 39.13/5.49      ( ~ v2_struct_0(sK8) ),
% 39.13/5.49      inference(cnf_transformation,[],[f70]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_42,plain,
% 39.13/5.49      ( v2_struct_0(sK8) != iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_8071,plain,
% 39.13/5.49      ( k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8)) = u1_struct_0(k1_tsep_1(sK5,sK6,sK8)) ),
% 39.13/5.49      inference(global_propositional_subsumption,
% 39.13/5.49                [status(thm)],
% 39.13/5.49                [c_6254,c_42]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_5304,plain,
% 39.13/5.49      ( k2_xboole_0(u1_struct_0(sK6),u1_struct_0(X0_53)) = u1_struct_0(k1_tsep_1(sK7,sK6,X0_53))
% 39.13/5.49      | m1_pre_topc(X0_53,sK7) != iProver_top
% 39.13/5.49      | v2_struct_0(X0_53) = iProver_top
% 39.13/5.49      | v2_struct_0(sK7) = iProver_top
% 39.13/5.49      | v2_struct_0(sK6) = iProver_top
% 39.13/5.49      | l1_pre_topc(sK7) != iProver_top ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_988,c_998]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_6009,plain,
% 39.13/5.49      ( v2_struct_0(X0_53) = iProver_top
% 39.13/5.49      | m1_pre_topc(X0_53,sK7) != iProver_top
% 39.13/5.49      | k2_xboole_0(u1_struct_0(sK6),u1_struct_0(X0_53)) = u1_struct_0(k1_tsep_1(sK7,sK6,X0_53)) ),
% 39.13/5.49      inference(global_propositional_subsumption,
% 39.13/5.49                [status(thm)],
% 39.13/5.49                [c_5304,c_37,c_38,c_40,c_1546]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_6010,plain,
% 39.13/5.49      ( k2_xboole_0(u1_struct_0(sK6),u1_struct_0(X0_53)) = u1_struct_0(k1_tsep_1(sK7,sK6,X0_53))
% 39.13/5.49      | m1_pre_topc(X0_53,sK7) != iProver_top
% 39.13/5.49      | v2_struct_0(X0_53) = iProver_top ),
% 39.13/5.49      inference(renaming,[status(thm)],[c_6009]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_6015,plain,
% 39.13/5.49      ( k2_xboole_0(k2_struct_0(sK6),u1_struct_0(X0_53)) = u1_struct_0(k1_tsep_1(sK7,sK6,X0_53))
% 39.13/5.49      | m1_pre_topc(X0_53,sK7) != iProver_top
% 39.13/5.49      | v2_struct_0(X0_53) = iProver_top ),
% 39.13/5.49      inference(light_normalisation,[status(thm)],[c_6010,c_4133]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_6022,plain,
% 39.13/5.49      ( k2_xboole_0(k2_struct_0(sK6),u1_struct_0(sK8)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK8))
% 39.13/5.49      | v2_struct_0(sK8) = iProver_top ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_987,c_6015]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_6048,plain,
% 39.13/5.49      ( k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK8))
% 39.13/5.49      | v2_struct_0(sK8) = iProver_top ),
% 39.13/5.49      inference(light_normalisation,[status(thm)],[c_6022,c_3967]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_7254,plain,
% 39.13/5.49      ( k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK8)) ),
% 39.13/5.49      inference(global_propositional_subsumption,
% 39.13/5.49                [status(thm)],
% 39.13/5.49                [c_6048,c_42]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_8074,plain,
% 39.13/5.49      ( u1_struct_0(k1_tsep_1(sK7,sK6,sK8)) = u1_struct_0(k1_tsep_1(sK5,sK6,sK8)) ),
% 39.13/5.49      inference(demodulation,[status(thm)],[c_8071,c_7254]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_17593,plain,
% 39.13/5.49      ( u1_struct_0(k1_tsep_1(sK5,sK6,sK8)) = k2_struct_0(k1_tsep_1(sK7,sK6,sK8))
% 39.13/5.49      | v2_struct_0(sK8) = iProver_top ),
% 39.13/5.49      inference(demodulation,[status(thm)],[c_17567,c_8074]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_90357,plain,
% 39.13/5.49      ( u1_struct_0(k1_tsep_1(sK5,sK6,sK8)) = k2_struct_0(k1_tsep_1(sK7,sK6,sK8)) ),
% 39.13/5.49      inference(global_propositional_subsumption,
% 39.13/5.49                [status(thm)],
% 39.13/5.49                [c_17593,c_42]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_17282,plain,
% 39.13/5.49      ( u1_struct_0(k1_tsep_1(sK5,sK6,X0_53)) = k2_struct_0(k1_tsep_1(sK5,sK6,X0_53))
% 39.13/5.49      | m1_pre_topc(X0_53,sK5) != iProver_top
% 39.13/5.49      | v2_struct_0(X0_53) = iProver_top
% 39.13/5.49      | v2_struct_0(sK6) = iProver_top
% 39.13/5.49      | v2_struct_0(sK5) = iProver_top
% 39.13/5.49      | l1_pre_topc(sK5) != iProver_top ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_993,c_15262]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_21694,plain,
% 39.13/5.49      ( v2_struct_0(X0_53) = iProver_top
% 39.13/5.49      | m1_pre_topc(X0_53,sK5) != iProver_top
% 39.13/5.49      | u1_struct_0(k1_tsep_1(sK5,sK6,X0_53)) = k2_struct_0(k1_tsep_1(sK5,sK6,X0_53)) ),
% 39.13/5.49      inference(global_propositional_subsumption,
% 39.13/5.49                [status(thm)],
% 39.13/5.49                [c_17282,c_35,c_37,c_38]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_21695,plain,
% 39.13/5.49      ( u1_struct_0(k1_tsep_1(sK5,sK6,X0_53)) = k2_struct_0(k1_tsep_1(sK5,sK6,X0_53))
% 39.13/5.49      | m1_pre_topc(X0_53,sK5) != iProver_top
% 39.13/5.49      | v2_struct_0(X0_53) = iProver_top ),
% 39.13/5.49      inference(renaming,[status(thm)],[c_21694]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_21703,plain,
% 39.13/5.49      ( u1_struct_0(k1_tsep_1(sK5,sK6,sK8)) = k2_struct_0(k1_tsep_1(sK5,sK6,sK8))
% 39.13/5.49      | v2_struct_0(sK8) = iProver_top ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_989,c_21695]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_21844,plain,
% 39.13/5.49      ( u1_struct_0(k1_tsep_1(sK5,sK6,sK8)) = k2_struct_0(k1_tsep_1(sK5,sK6,sK8)) ),
% 39.13/5.49      inference(global_propositional_subsumption,
% 39.13/5.49                [status(thm)],
% 39.13/5.49                [c_21703,c_42]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_90359,plain,
% 39.13/5.49      ( k2_struct_0(k1_tsep_1(sK5,sK6,sK8)) = k2_struct_0(k1_tsep_1(sK7,sK6,sK8)) ),
% 39.13/5.49      inference(light_normalisation,[status(thm)],[c_90357,c_21844]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_12,plain,
% 39.13/5.49      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~ sP0(X0,X1) ),
% 39.13/5.49      inference(cnf_transformation,[],[f43]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_335,plain,
% 39.13/5.49      ( r1_tarski(k2_struct_0(X0_53),k2_struct_0(X1_53))
% 39.13/5.49      | ~ sP0(X0_53,X1_53) ),
% 39.13/5.49      inference(subtyping,[status(esa)],[c_12]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_976,plain,
% 39.13/5.49      ( r1_tarski(k2_struct_0(X0_53),k2_struct_0(X1_53)) = iProver_top
% 39.13/5.49      | sP0(X0_53,X1_53) != iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_335]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_90366,plain,
% 39.13/5.49      ( r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK8)),k2_struct_0(X0_53)) = iProver_top
% 39.13/5.49      | sP0(k1_tsep_1(sK7,sK6,sK8),X0_53) != iProver_top ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_90359,c_976]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_991,plain,
% 39.13/5.49      ( m1_pre_topc(sK7,sK5) = iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_320]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_1964,plain,
% 39.13/5.49      ( l1_pre_topc(sK7) = iProver_top
% 39.13/5.49      | l1_pre_topc(sK5) != iProver_top ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_991,c_979]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_2889,plain,
% 39.13/5.49      ( l1_pre_topc(sK7) = iProver_top ),
% 39.13/5.49      inference(global_propositional_subsumption,
% 39.13/5.49                [status(thm)],
% 39.13/5.49                [c_1964,c_37,c_1546]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_2894,plain,
% 39.13/5.49      ( l1_struct_0(sK7) = iProver_top ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_2889,c_978]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_4712,plain,
% 39.13/5.49      ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_2894,c_964]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_22,plain,
% 39.13/5.49      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 39.13/5.49      | ~ m1_pre_topc(X0,X2)
% 39.13/5.49      | ~ m1_pre_topc(X1,X2)
% 39.13/5.49      | m1_pre_topc(X0,X1)
% 39.13/5.49      | ~ v2_pre_topc(X2)
% 39.13/5.49      | ~ l1_pre_topc(X2) ),
% 39.13/5.49      inference(cnf_transformation,[],[f61]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_326,plain,
% 39.13/5.49      ( ~ r1_tarski(u1_struct_0(X0_53),u1_struct_0(X1_53))
% 39.13/5.49      | ~ m1_pre_topc(X0_53,X2_53)
% 39.13/5.49      | ~ m1_pre_topc(X1_53,X2_53)
% 39.13/5.49      | m1_pre_topc(X0_53,X1_53)
% 39.13/5.49      | ~ v2_pre_topc(X2_53)
% 39.13/5.49      | ~ l1_pre_topc(X2_53) ),
% 39.13/5.49      inference(subtyping,[status(esa)],[c_22]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_985,plain,
% 39.13/5.49      ( r1_tarski(u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 39.13/5.49      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 39.13/5.49      | m1_pre_topc(X1_53,X2_53) != iProver_top
% 39.13/5.49      | m1_pre_topc(X0_53,X1_53) = iProver_top
% 39.13/5.49      | v2_pre_topc(X2_53) != iProver_top
% 39.13/5.49      | l1_pre_topc(X2_53) != iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_326]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_5785,plain,
% 39.13/5.49      ( r1_tarski(u1_struct_0(X0_53),k2_struct_0(sK7)) != iProver_top
% 39.13/5.49      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 39.13/5.49      | m1_pre_topc(X0_53,sK7) = iProver_top
% 39.13/5.49      | m1_pre_topc(sK7,X1_53) != iProver_top
% 39.13/5.49      | v2_pre_topc(X1_53) != iProver_top
% 39.13/5.49      | l1_pre_topc(X1_53) != iProver_top ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_4712,c_985]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_21900,plain,
% 39.13/5.49      ( r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK8)),k2_struct_0(sK7)) != iProver_top
% 39.13/5.49      | m1_pre_topc(k1_tsep_1(sK5,sK6,sK8),X0_53) != iProver_top
% 39.13/5.49      | m1_pre_topc(k1_tsep_1(sK5,sK6,sK8),sK7) = iProver_top
% 39.13/5.49      | m1_pre_topc(sK7,X0_53) != iProver_top
% 39.13/5.49      | v2_pre_topc(X0_53) != iProver_top
% 39.13/5.49      | l1_pre_topc(X0_53) != iProver_top ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_21844,c_5785]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_33,negated_conjecture,
% 39.13/5.49      ( v2_pre_topc(sK5) ),
% 39.13/5.49      inference(cnf_transformation,[],[f64]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_36,plain,
% 39.13/5.49      ( v2_pre_topc(sK5) = iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_39,plain,
% 39.13/5.49      ( m1_pre_topc(sK6,sK5) = iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_41,plain,
% 39.13/5.49      ( m1_pre_topc(sK7,sK5) = iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_43,plain,
% 39.13/5.49      ( m1_pre_topc(sK8,sK5) = iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_23,negated_conjecture,
% 39.13/5.49      ( ~ m1_pre_topc(k1_tsep_1(sK5,sK6,sK8),sK7) ),
% 39.13/5.49      inference(cnf_transformation,[],[f74]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_46,plain,
% 39.13/5.49      ( m1_pre_topc(k1_tsep_1(sK5,sK6,sK8),sK7) != iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_1459,plain,
% 39.13/5.49      ( ~ m1_pre_topc(X0_53,sK5)
% 39.13/5.49      | m1_pre_topc(k1_tsep_1(sK5,X0_53,sK8),sK5)
% 39.13/5.49      | ~ m1_pre_topc(sK8,sK5)
% 39.13/5.49      | v2_struct_0(X0_53)
% 39.13/5.49      | v2_struct_0(sK8)
% 39.13/5.49      | v2_struct_0(sK5)
% 39.13/5.49      | ~ l1_pre_topc(sK5) ),
% 39.13/5.49      inference(instantiation,[status(thm)],[c_330]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_1895,plain,
% 39.13/5.49      ( m1_pre_topc(k1_tsep_1(sK5,sK6,sK8),sK5)
% 39.13/5.49      | ~ m1_pre_topc(sK8,sK5)
% 39.13/5.49      | ~ m1_pre_topc(sK6,sK5)
% 39.13/5.49      | v2_struct_0(sK8)
% 39.13/5.49      | v2_struct_0(sK6)
% 39.13/5.49      | v2_struct_0(sK5)
% 39.13/5.49      | ~ l1_pre_topc(sK5) ),
% 39.13/5.49      inference(instantiation,[status(thm)],[c_1459]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_1896,plain,
% 39.13/5.49      ( m1_pre_topc(k1_tsep_1(sK5,sK6,sK8),sK5) = iProver_top
% 39.13/5.49      | m1_pre_topc(sK8,sK5) != iProver_top
% 39.13/5.49      | m1_pre_topc(sK6,sK5) != iProver_top
% 39.13/5.49      | v2_struct_0(sK8) = iProver_top
% 39.13/5.49      | v2_struct_0(sK6) = iProver_top
% 39.13/5.49      | v2_struct_0(sK5) = iProver_top
% 39.13/5.49      | l1_pre_topc(sK5) != iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_1895]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_22268,plain,
% 39.13/5.49      ( r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK8)),k2_struct_0(sK7)) != iProver_top
% 39.13/5.49      | m1_pre_topc(k1_tsep_1(sK5,sK6,sK8),sK7) = iProver_top
% 39.13/5.49      | m1_pre_topc(k1_tsep_1(sK5,sK6,sK8),sK5) != iProver_top
% 39.13/5.49      | m1_pre_topc(sK7,sK5) != iProver_top
% 39.13/5.49      | v2_pre_topc(sK5) != iProver_top
% 39.13/5.49      | l1_pre_topc(sK5) != iProver_top ),
% 39.13/5.49      inference(instantiation,[status(thm)],[c_21900]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_58207,plain,
% 39.13/5.49      ( r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK8)),k2_struct_0(sK7)) != iProver_top ),
% 39.13/5.49      inference(global_propositional_subsumption,
% 39.13/5.49                [status(thm)],
% 39.13/5.49                [c_21900,c_35,c_36,c_37,c_38,c_39,c_41,c_42,c_43,c_46,
% 39.13/5.49                 c_1896,c_22268]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_101939,plain,
% 39.13/5.49      ( sP0(k1_tsep_1(sK7,sK6,sK8),sK7) != iProver_top ),
% 39.13/5.49      inference(superposition,[status(thm)],[c_90366,c_58207]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_8394,plain,
% 39.13/5.49      ( ~ m1_pre_topc(k1_tsep_1(sK7,sK6,sK8),X0_53)
% 39.13/5.49      | ~ l1_pre_topc(X0_53)
% 39.13/5.49      | l1_pre_topc(k1_tsep_1(sK7,sK6,sK8)) ),
% 39.13/5.49      inference(instantiation,[status(thm)],[c_332]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_54145,plain,
% 39.13/5.49      ( ~ m1_pre_topc(k1_tsep_1(sK7,sK6,sK8),sK7)
% 39.13/5.49      | l1_pre_topc(k1_tsep_1(sK7,sK6,sK8))
% 39.13/5.49      | ~ l1_pre_topc(sK7) ),
% 39.13/5.49      inference(instantiation,[status(thm)],[c_8394]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_54146,plain,
% 39.13/5.49      ( m1_pre_topc(k1_tsep_1(sK7,sK6,sK8),sK7) != iProver_top
% 39.13/5.49      | l1_pre_topc(k1_tsep_1(sK7,sK6,sK8)) = iProver_top
% 39.13/5.49      | l1_pre_topc(sK7) != iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_54145]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_13,plain,
% 39.13/5.49      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 39.13/5.49      inference(cnf_transformation,[],[f53]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_334,plain,
% 39.13/5.49      ( sP1(X0_53,X1_53) | ~ l1_pre_topc(X1_53) | ~ l1_pre_topc(X0_53) ),
% 39.13/5.49      inference(subtyping,[status(esa)],[c_13]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_3609,plain,
% 39.13/5.49      ( sP1(sK7,k1_tsep_1(sK7,sK6,sK8))
% 39.13/5.49      | ~ l1_pre_topc(k1_tsep_1(sK7,sK6,sK8))
% 39.13/5.49      | ~ l1_pre_topc(sK7) ),
% 39.13/5.49      inference(instantiation,[status(thm)],[c_334]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_3610,plain,
% 39.13/5.49      ( sP1(sK7,k1_tsep_1(sK7,sK6,sK8)) = iProver_top
% 39.13/5.49      | l1_pre_topc(k1_tsep_1(sK7,sK6,sK8)) != iProver_top
% 39.13/5.49      | l1_pre_topc(sK7) != iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_3609]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_2,plain,
% 39.13/5.49      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 39.13/5.49      inference(cnf_transformation,[],[f41]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_345,plain,
% 39.13/5.49      ( ~ sP1(X0_53,X1_53)
% 39.13/5.49      | sP0(X1_53,X0_53)
% 39.13/5.49      | ~ m1_pre_topc(X1_53,X0_53) ),
% 39.13/5.49      inference(subtyping,[status(esa)],[c_2]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_2262,plain,
% 39.13/5.49      ( ~ sP1(sK7,k1_tsep_1(sK7,sK6,sK8))
% 39.13/5.49      | sP0(k1_tsep_1(sK7,sK6,sK8),sK7)
% 39.13/5.49      | ~ m1_pre_topc(k1_tsep_1(sK7,sK6,sK8),sK7) ),
% 39.13/5.49      inference(instantiation,[status(thm)],[c_345]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_2263,plain,
% 39.13/5.49      ( sP1(sK7,k1_tsep_1(sK7,sK6,sK8)) != iProver_top
% 39.13/5.49      | sP0(k1_tsep_1(sK7,sK6,sK8),sK7) = iProver_top
% 39.13/5.49      | m1_pre_topc(k1_tsep_1(sK7,sK6,sK8),sK7) != iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_2262]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_1449,plain,
% 39.13/5.49      ( ~ m1_pre_topc(X0_53,sK7)
% 39.13/5.49      | m1_pre_topc(k1_tsep_1(sK7,X0_53,sK8),sK7)
% 39.13/5.49      | ~ m1_pre_topc(sK8,sK7)
% 39.13/5.49      | v2_struct_0(X0_53)
% 39.13/5.49      | v2_struct_0(sK7)
% 39.13/5.49      | v2_struct_0(sK8)
% 39.13/5.49      | ~ l1_pre_topc(sK7) ),
% 39.13/5.49      inference(instantiation,[status(thm)],[c_330]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_1860,plain,
% 39.13/5.49      ( m1_pre_topc(k1_tsep_1(sK7,sK6,sK8),sK7)
% 39.13/5.49      | ~ m1_pre_topc(sK8,sK7)
% 39.13/5.49      | ~ m1_pre_topc(sK6,sK7)
% 39.13/5.49      | v2_struct_0(sK7)
% 39.13/5.49      | v2_struct_0(sK8)
% 39.13/5.49      | v2_struct_0(sK6)
% 39.13/5.49      | ~ l1_pre_topc(sK7) ),
% 39.13/5.49      inference(instantiation,[status(thm)],[c_1449]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_1861,plain,
% 39.13/5.49      ( m1_pre_topc(k1_tsep_1(sK7,sK6,sK8),sK7) = iProver_top
% 39.13/5.49      | m1_pre_topc(sK8,sK7) != iProver_top
% 39.13/5.49      | m1_pre_topc(sK6,sK7) != iProver_top
% 39.13/5.49      | v2_struct_0(sK7) = iProver_top
% 39.13/5.49      | v2_struct_0(sK8) = iProver_top
% 39.13/5.49      | v2_struct_0(sK6) = iProver_top
% 39.13/5.49      | l1_pre_topc(sK7) != iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_1860]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_45,plain,
% 39.13/5.49      ( m1_pre_topc(sK8,sK7) = iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(c_44,plain,
% 39.13/5.49      ( m1_pre_topc(sK6,sK7) = iProver_top ),
% 39.13/5.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 39.13/5.49  
% 39.13/5.49  cnf(contradiction,plain,
% 39.13/5.49      ( $false ),
% 39.13/5.49      inference(minisat,
% 39.13/5.49                [status(thm)],
% 39.13/5.49                [c_101939,c_54146,c_3610,c_2263,c_1861,c_1546,c_45,c_44,
% 39.13/5.49                 c_42,c_40,c_38,c_37]) ).
% 39.13/5.49  
% 39.13/5.49  
% 39.13/5.49  % SZS output end CNFRefutation for theBenchmark.p
% 39.13/5.49  
% 39.13/5.49  ------                               Statistics
% 39.13/5.49  
% 39.13/5.49  ------ Selected
% 39.13/5.49  
% 39.13/5.49  total_time:                             4.914
% 39.13/5.49  
%------------------------------------------------------------------------------
