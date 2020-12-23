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
% DateTime   : Thu Dec  3 12:22:11 EST 2020

% Result     : Theorem 27.76s
% Output     : CNFRefutation 27.76s
% Verified   : 
% Statistics : Number of formulae       :  205 (1696 expanded)
%              Number of clauses        :  141 ( 502 expanded)
%              Number of leaves         :   17 ( 545 expanded)
%              Depth                    :   22
%              Number of atoms          :  953 (16164 expanded)
%              Number of equality atoms :  266 ( 733 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   26 (   3 average)
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
                 => ( ( m1_pre_topc(X2,X3)
                      & m1_pre_topc(X1,X3) )
                   => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                      | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
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
                   => ( ( m1_pre_topc(X2,X3)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                        | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
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
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
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
          ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
          & ~ r1_tsep_1(X1,X2)
          & m1_pre_topc(X2,X3)
          & m1_pre_topc(X1,X3)
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),sK8)
        & ~ r1_tsep_1(X1,X2)
        & m1_pre_topc(X2,sK8)
        & m1_pre_topc(X1,sK8)
        & m1_pre_topc(sK8,X0)
        & ~ v2_struct_0(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X3)
              & m1_pre_topc(X1,X3)
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ m1_pre_topc(k2_tsep_1(X0,X1,sK7),X3)
            & ~ r1_tsep_1(X1,sK7)
            & m1_pre_topc(sK7,X3)
            & m1_pre_topc(X1,X3)
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
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k2_tsep_1(X0,sK6,X2),X3)
                & ~ r1_tsep_1(sK6,X2)
                & m1_pre_topc(X2,X3)
                & m1_pre_topc(sK6,X3)
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
                    ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X1,X3)
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
                  ( ~ m1_pre_topc(k2_tsep_1(sK5,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
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
    ( ~ m1_pre_topc(k2_tsep_1(sK5,sK6,sK7),sK8)
    & ~ r1_tsep_1(sK6,sK7)
    & m1_pre_topc(sK7,sK8)
    & m1_pre_topc(sK6,sK8)
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
    m1_pre_topc(sK7,sK8) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    m1_pre_topc(sK6,sK8) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
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

fof(f70,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,(
    m1_pre_topc(sK8,sK5) ),
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
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
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
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
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
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k2_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f74,plain,(
    ~ r1_tsep_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    m1_pre_topc(sK6,sK5) ),
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

fof(f75,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK5,sK6,sK7),sK8) ),
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

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK7,sK8) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3213,negated_conjecture,
    ( m1_pre_topc(sK7,sK8) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_88727,plain,
    ( m1_pre_topc(sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3213])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK6,sK8) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3212,negated_conjecture,
    ( m1_pre_topc(sK6,sK8) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_88726,plain,
    ( m1_pre_topc(sK6,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3212])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3217,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X2_54,X1_54)
    | m1_pre_topc(k2_tsep_1(X1_54,X0_54,X2_54),X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_88709,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | m1_pre_topc(k2_tsep_1(X1_54,X0_54,X2_54),X1_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3217])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3218,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_88708,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3218])).

cnf(c_89248,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(k2_tsep_1(X1_54,X0_54,X2_54)) = iProver_top ),
    inference(superposition,[status(thm)],[c_88709,c_88708])).

cnf(c_14,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_0,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_386,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_14,c_0])).

cnf(c_3203,plain,
    ( ~ l1_pre_topc(X0_54)
    | u1_struct_0(X0_54) = k2_struct_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_386])).

cnf(c_88712,plain,
    ( u1_struct_0(X0_54) = k2_struct_0(X0_54)
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3203])).

cnf(c_89414,plain,
    ( u1_struct_0(k2_tsep_1(X0_54,X1_54,X2_54)) = k2_struct_0(k2_tsep_1(X0_54,X1_54,X2_54))
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_89248,c_88712])).

cnf(c_90040,plain,
    ( u1_struct_0(k2_tsep_1(sK8,sK6,X0_54)) = k2_struct_0(k2_tsep_1(sK8,sK6,X0_54))
    | m1_pre_topc(X0_54,sK8) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_88726,c_89414])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_38,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_39,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_43,plain,
    ( v2_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_44,plain,
    ( m1_pre_topc(sK8,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4826,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | l1_pre_topc(sK8)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_3218])).

cnf(c_4827,plain,
    ( m1_pre_topc(sK8,sK5) != iProver_top
    | l1_pre_topc(sK8) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4826])).

cnf(c_32308,plain,
    ( m1_pre_topc(sK6,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3212])).

cnf(c_32293,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | m1_pre_topc(k2_tsep_1(X1_54,X0_54,X2_54),X1_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3217])).

cnf(c_32292,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3218])).

cnf(c_32888,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(k2_tsep_1(X1_54,X0_54,X2_54)) = iProver_top ),
    inference(superposition,[status(thm)],[c_32293,c_32292])).

cnf(c_32295,plain,
    ( u1_struct_0(X0_54) = k2_struct_0(X0_54)
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3203])).

cnf(c_33452,plain,
    ( u1_struct_0(k2_tsep_1(X0_54,X1_54,X2_54)) = k2_struct_0(k2_tsep_1(X0_54,X1_54,X2_54))
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_32888,c_32295])).

cnf(c_34044,plain,
    ( u1_struct_0(k2_tsep_1(sK8,sK6,X0_54)) = k2_struct_0(k2_tsep_1(sK8,sK6,X0_54))
    | m1_pre_topc(X0_54,sK8) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_32308,c_33452])).

cnf(c_90518,plain,
    ( v2_struct_0(X0_54) = iProver_top
    | m1_pre_topc(X0_54,sK8) != iProver_top
    | u1_struct_0(k2_tsep_1(sK8,sK6,X0_54)) = k2_struct_0(k2_tsep_1(sK8,sK6,X0_54)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_90040,c_38,c_39,c_43,c_44,c_4827,c_34044])).

cnf(c_90519,plain,
    ( u1_struct_0(k2_tsep_1(sK8,sK6,X0_54)) = k2_struct_0(k2_tsep_1(sK8,sK6,X0_54))
    | m1_pre_topc(X0_54,sK8) != iProver_top
    | v2_struct_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_90518])).

cnf(c_90525,plain,
    ( u1_struct_0(k2_tsep_1(sK8,sK6,sK7)) = k2_struct_0(k2_tsep_1(sK8,sK6,sK7))
    | v2_struct_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_88727,c_90519])).

cnf(c_17,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(k2_tsep_1(X2,X0,X1),X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k2_tsep_1(X2,X0,X1))
    | ~ v1_pre_topc(k2_tsep_1(X2,X0,X1))
    | ~ l1_pre_topc(X2)
    | u1_struct_0(k2_tsep_1(X2,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tsep_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_498,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(k2_tsep_1(X1,X0,X2))
    | ~ v1_pre_topc(k2_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k2_tsep_1(X1,X0,X2)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X2))
    | sK7 != X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_499,plain,
    ( ~ m1_pre_topc(k2_tsep_1(X0,sK6,sK7),X0)
    | ~ m1_pre_topc(sK7,X0)
    | ~ m1_pre_topc(sK6,X0)
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(X0,sK6,sK7))
    | v2_struct_0(sK7)
    | v2_struct_0(sK6)
    | ~ v1_pre_topc(k2_tsep_1(X0,sK6,sK7))
    | ~ l1_pre_topc(X0)
    | u1_struct_0(k2_tsep_1(X0,sK6,sK7)) = k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_503,plain,
    ( ~ m1_pre_topc(k2_tsep_1(X0,sK6,sK7),X0)
    | ~ m1_pre_topc(sK7,X0)
    | ~ m1_pre_topc(sK6,X0)
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(X0,sK6,sK7))
    | ~ v1_pre_topc(k2_tsep_1(X0,sK6,sK7))
    | ~ l1_pre_topc(X0)
    | u1_struct_0(k2_tsep_1(X0,sK6,sK7)) = k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_499,c_32,c_30])).

cnf(c_3198,plain,
    ( ~ m1_pre_topc(k2_tsep_1(X0_54,sK6,sK7),X0_54)
    | ~ m1_pre_topc(sK7,X0_54)
    | ~ m1_pre_topc(sK6,X0_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(k2_tsep_1(X0_54,sK6,sK7))
    | ~ v1_pre_topc(k2_tsep_1(X0_54,sK6,sK7))
    | ~ l1_pre_topc(X0_54)
    | u1_struct_0(k2_tsep_1(X0_54,sK6,sK7)) = k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_503])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k2_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3215,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X2_54,X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | ~ v2_struct_0(k2_tsep_1(X1_54,X0_54,X2_54))
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_14147,plain,
    ( ~ m1_pre_topc(sK7,X0_54)
    | ~ m1_pre_topc(sK6,X0_54)
    | v2_struct_0(X0_54)
    | ~ v2_struct_0(k2_tsep_1(X0_54,sK6,sK7))
    | v2_struct_0(sK7)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(X0_54) ),
    inference(instantiation,[status(thm)],[c_3215])).

cnf(c_34725,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | m1_pre_topc(k2_tsep_1(X1_54,sK6,X0_54),X1_54)
    | ~ m1_pre_topc(sK6,X1_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(X1_54) ),
    inference(instantiation,[status(thm)],[c_3217])).

cnf(c_39135,plain,
    ( m1_pre_topc(k2_tsep_1(X0_54,sK6,sK7),X0_54)
    | ~ m1_pre_topc(sK7,X0_54)
    | ~ m1_pre_topc(sK6,X0_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(X0_54) ),
    inference(instantiation,[status(thm)],[c_34725])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v1_pre_topc(k2_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3216,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X2_54,X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | v1_pre_topc(k2_tsep_1(X1_54,X0_54,X2_54))
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_58490,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(sK6,X1_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK6)
    | v1_pre_topc(k2_tsep_1(X1_54,sK6,X0_54))
    | ~ l1_pre_topc(X1_54) ),
    inference(instantiation,[status(thm)],[c_3216])).

cnf(c_68681,plain,
    ( ~ m1_pre_topc(sK7,X0_54)
    | ~ m1_pre_topc(sK6,X0_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6)
    | v1_pre_topc(k2_tsep_1(X0_54,sK6,sK7))
    | ~ l1_pre_topc(X0_54) ),
    inference(instantiation,[status(thm)],[c_58490])).

cnf(c_88417,plain,
    ( ~ m1_pre_topc(sK7,X0_54)
    | ~ m1_pre_topc(sK6,X0_54)
    | v2_struct_0(X0_54)
    | ~ l1_pre_topc(X0_54)
    | u1_struct_0(k2_tsep_1(X0_54,sK6,sK7)) = k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3198,c_32,c_30,c_14147,c_39135,c_68681])).

cnf(c_88542,plain,
    ( ~ m1_pre_topc(sK7,X0_54)
    | ~ m1_pre_topc(sK6,X0_54)
    | v2_struct_0(X0_54)
    | ~ l1_pre_topc(X0_54)
    | u1_struct_0(k2_tsep_1(X0_54,sK6,sK7)) = k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3198,c_88417])).

cnf(c_88701,plain,
    ( u1_struct_0(k2_tsep_1(X0_54,sK6,sK7)) = k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7))
    | m1_pre_topc(sK7,X0_54) != iProver_top
    | m1_pre_topc(sK6,X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_88542])).

cnf(c_88974,plain,
    ( k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) = u1_struct_0(k2_tsep_1(sK8,sK6,sK7))
    | m1_pre_topc(sK6,sK8) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_88727,c_88701])).

cnf(c_45,plain,
    ( m1_pre_topc(sK6,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_89063,plain,
    ( k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) = u1_struct_0(k2_tsep_1(sK8,sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_88974,c_38,c_43,c_44,c_45,c_4827])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3209,negated_conjecture,
    ( m1_pre_topc(sK7,sK5) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_88723,plain,
    ( m1_pre_topc(sK7,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3209])).

cnf(c_88947,plain,
    ( k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) = u1_struct_0(k2_tsep_1(sK5,sK6,sK7))
    | m1_pre_topc(sK6,sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_88723,c_88701])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_36,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_40,plain,
    ( m1_pre_topc(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_89055,plain,
    ( k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) = u1_struct_0(k2_tsep_1(sK5,sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_88947,c_36,c_38,c_40])).

cnf(c_89065,plain,
    ( u1_struct_0(k2_tsep_1(sK8,sK6,sK7)) = u1_struct_0(k2_tsep_1(sK5,sK6,sK7)) ),
    inference(light_normalisation,[status(thm)],[c_89063,c_89055])).

cnf(c_90550,plain,
    ( u1_struct_0(k2_tsep_1(sK5,sK6,sK7)) = k2_struct_0(k2_tsep_1(sK8,sK6,sK7))
    | v2_struct_0(sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_90525,c_89065])).

cnf(c_41,plain,
    ( v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_143903,plain,
    ( u1_struct_0(k2_tsep_1(sK5,sK6,sK7)) = k2_struct_0(k2_tsep_1(sK8,sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_90550,c_41])).

cnf(c_3207,negated_conjecture,
    ( m1_pre_topc(sK6,sK5) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_88721,plain,
    ( m1_pre_topc(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3207])).

cnf(c_90043,plain,
    ( u1_struct_0(k2_tsep_1(sK5,sK6,X0_54)) = k2_struct_0(k2_tsep_1(sK5,sK6,X0_54))
    | m1_pre_topc(X0_54,sK5) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_88721,c_89414])).

cnf(c_32303,plain,
    ( m1_pre_topc(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3207])).

cnf(c_34047,plain,
    ( u1_struct_0(k2_tsep_1(sK5,sK6,X0_54)) = k2_struct_0(k2_tsep_1(sK5,sK6,X0_54))
    | m1_pre_topc(X0_54,sK5) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_32303,c_33452])).

cnf(c_35912,plain,
    ( v2_struct_0(X0_54) = iProver_top
    | m1_pre_topc(X0_54,sK5) != iProver_top
    | u1_struct_0(k2_tsep_1(sK5,sK6,X0_54)) = k2_struct_0(k2_tsep_1(sK5,sK6,X0_54)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34047,c_36,c_38,c_39])).

cnf(c_35913,plain,
    ( u1_struct_0(k2_tsep_1(sK5,sK6,X0_54)) = k2_struct_0(k2_tsep_1(sK5,sK6,X0_54))
    | m1_pre_topc(X0_54,sK5) != iProver_top
    | v2_struct_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_35912])).

cnf(c_91887,plain,
    ( v2_struct_0(X0_54) = iProver_top
    | m1_pre_topc(X0_54,sK5) != iProver_top
    | u1_struct_0(k2_tsep_1(sK5,sK6,X0_54)) = k2_struct_0(k2_tsep_1(sK5,sK6,X0_54)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_90043,c_36,c_38,c_39,c_34047])).

cnf(c_91888,plain,
    ( u1_struct_0(k2_tsep_1(sK5,sK6,X0_54)) = k2_struct_0(k2_tsep_1(sK5,sK6,X0_54))
    | m1_pre_topc(X0_54,sK5) != iProver_top
    | v2_struct_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_91887])).

cnf(c_91895,plain,
    ( u1_struct_0(k2_tsep_1(sK5,sK6,sK7)) = k2_struct_0(k2_tsep_1(sK5,sK6,sK7))
    | v2_struct_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_88723,c_91888])).

cnf(c_32305,plain,
    ( m1_pre_topc(sK7,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3209])).

cnf(c_35922,plain,
    ( u1_struct_0(k2_tsep_1(sK5,sK6,sK7)) = k2_struct_0(k2_tsep_1(sK5,sK6,sK7))
    | v2_struct_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_32305,c_35913])).

cnf(c_92079,plain,
    ( u1_struct_0(k2_tsep_1(sK5,sK6,sK7)) = k2_struct_0(k2_tsep_1(sK5,sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_91895,c_41,c_35922])).

cnf(c_143905,plain,
    ( k2_struct_0(k2_tsep_1(sK5,sK6,sK7)) = k2_struct_0(k2_tsep_1(sK8,sK6,sK7)) ),
    inference(light_normalisation,[status(thm)],[c_143903,c_92079])).

cnf(c_12,plain,
    ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
    | ~ sP0(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3219,plain,
    ( r1_tarski(k2_struct_0(X0_54),k2_struct_0(X1_54))
    | ~ sP0(X0_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_88707,plain,
    ( r1_tarski(k2_struct_0(X0_54),k2_struct_0(X1_54)) = iProver_top
    | sP0(X0_54,X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3219])).

cnf(c_143907,plain,
    ( r1_tarski(k2_struct_0(k2_tsep_1(sK5,sK6,sK7)),k2_struct_0(X0_54)) = iProver_top
    | sP0(k2_tsep_1(sK8,sK6,sK7),X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_143905,c_88707])).

cnf(c_3211,negated_conjecture,
    ( m1_pre_topc(sK8,sK5) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_88725,plain,
    ( m1_pre_topc(sK8,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3211])).

cnf(c_89190,plain,
    ( l1_pre_topc(sK8) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_88725,c_88708])).

cnf(c_89290,plain,
    ( l1_pre_topc(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_89190,c_38,c_44,c_4827])).

cnf(c_89344,plain,
    ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(superposition,[status(thm)],[c_89290,c_88712])).

cnf(c_22,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_444,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_34])).

cnf(c_445,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK5)
    | ~ m1_pre_topc(X0,sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_447,plain,
    ( ~ m1_pre_topc(X0,sK5)
    | ~ m1_pre_topc(X1,sK5)
    | m1_pre_topc(X0,X1)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_33])).

cnf(c_448,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK5)
    | ~ m1_pre_topc(X0,sK5) ),
    inference(renaming,[status(thm)],[c_447])).

cnf(c_3200,plain,
    ( ~ r1_tarski(u1_struct_0(X0_54),u1_struct_0(X1_54))
    | m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X1_54,sK5)
    | ~ m1_pre_topc(X0_54,sK5) ),
    inference(subtyping,[status(esa)],[c_448])).

cnf(c_88715,plain,
    ( r1_tarski(u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X0_54,X1_54) = iProver_top
    | m1_pre_topc(X1_54,sK5) != iProver_top
    | m1_pre_topc(X0_54,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3200])).

cnf(c_89423,plain,
    ( r1_tarski(u1_struct_0(X0_54),k2_struct_0(sK8)) != iProver_top
    | m1_pre_topc(X0_54,sK8) = iProver_top
    | m1_pre_topc(X0_54,sK5) != iProver_top
    | m1_pre_topc(sK8,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_89344,c_88715])).

cnf(c_32307,plain,
    ( m1_pre_topc(sK8,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3211])).

cnf(c_32848,plain,
    ( l1_pre_topc(sK8) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_32307,c_32292])).

cnf(c_32973,plain,
    ( l1_pre_topc(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32848,c_38,c_44,c_4827])).

cnf(c_32978,plain,
    ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(superposition,[status(thm)],[c_32973,c_32295])).

cnf(c_32298,plain,
    ( r1_tarski(u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X0_54,X1_54) = iProver_top
    | m1_pre_topc(X1_54,sK5) != iProver_top
    | m1_pre_topc(X0_54,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3200])).

cnf(c_33318,plain,
    ( r1_tarski(u1_struct_0(X0_54),k2_struct_0(sK8)) != iProver_top
    | m1_pre_topc(X0_54,sK8) = iProver_top
    | m1_pre_topc(X0_54,sK5) != iProver_top
    | m1_pre_topc(sK8,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_32978,c_32298])).

cnf(c_89923,plain,
    ( m1_pre_topc(X0_54,sK5) != iProver_top
    | m1_pre_topc(X0_54,sK8) = iProver_top
    | r1_tarski(u1_struct_0(X0_54),k2_struct_0(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_89423,c_44,c_33318])).

cnf(c_89924,plain,
    ( r1_tarski(u1_struct_0(X0_54),k2_struct_0(sK8)) != iProver_top
    | m1_pre_topc(X0_54,sK8) = iProver_top
    | m1_pre_topc(X0_54,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_89923])).

cnf(c_92124,plain,
    ( r1_tarski(k2_struct_0(k2_tsep_1(sK5,sK6,sK7)),k2_struct_0(sK8)) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK5,sK6,sK7),sK8) = iProver_top
    | m1_pre_topc(k2_tsep_1(sK5,sK6,sK7),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_92079,c_89924])).

cnf(c_42,plain,
    ( m1_pre_topc(sK7,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_23,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(sK5,sK6,sK7),sK8) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_48,plain,
    ( m1_pre_topc(k2_tsep_1(sK5,sK6,sK7),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7763,plain,
    ( ~ m1_pre_topc(X0_54,sK5)
    | m1_pre_topc(k2_tsep_1(sK5,sK6,X0_54),sK5)
    | ~ m1_pre_topc(sK6,sK5)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_3217])).

cnf(c_7895,plain,
    ( m1_pre_topc(k2_tsep_1(sK5,sK6,sK7),sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ m1_pre_topc(sK6,sK5)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_7763])).

cnf(c_7896,plain,
    ( m1_pre_topc(k2_tsep_1(sK5,sK6,sK7),sK5) = iProver_top
    | m1_pre_topc(sK7,sK5) != iProver_top
    | m1_pre_topc(sK6,sK5) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7895])).

cnf(c_36147,plain,
    ( u1_struct_0(k2_tsep_1(sK5,sK6,sK7)) = k2_struct_0(k2_tsep_1(sK5,sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_35922,c_41])).

cnf(c_44030,plain,
    ( m1_pre_topc(X0_54,sK5) != iProver_top
    | m1_pre_topc(X0_54,sK8) = iProver_top
    | r1_tarski(u1_struct_0(X0_54),k2_struct_0(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33318,c_44])).

cnf(c_44031,plain,
    ( r1_tarski(u1_struct_0(X0_54),k2_struct_0(sK8)) != iProver_top
    | m1_pre_topc(X0_54,sK8) = iProver_top
    | m1_pre_topc(X0_54,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_44030])).

cnf(c_44043,plain,
    ( r1_tarski(k2_struct_0(k2_tsep_1(sK5,sK6,sK7)),k2_struct_0(sK8)) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK5,sK6,sK7),sK8) = iProver_top
    | m1_pre_topc(k2_tsep_1(sK5,sK6,sK7),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_36147,c_44031])).

cnf(c_112639,plain,
    ( r1_tarski(k2_struct_0(k2_tsep_1(sK5,sK6,sK7)),k2_struct_0(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_92124,c_36,c_38,c_39,c_40,c_41,c_42,c_48,c_7896,c_44043])).

cnf(c_143933,plain,
    ( sP0(k2_tsep_1(sK8,sK6,sK7),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_143907,c_112639])).

cnf(c_13,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_400,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_13,c_2])).

cnf(c_404,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X0,X1)
    | sP0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_400,c_15])).

cnf(c_405,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_404])).

cnf(c_3202,plain,
    ( sP0(X0_54,X1_54)
    | ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_405])).

cnf(c_17353,plain,
    ( sP0(k2_tsep_1(sK8,sK6,sK7),sK8)
    | ~ m1_pre_topc(k2_tsep_1(sK8,sK6,sK7),sK8)
    | ~ l1_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_3202])).

cnf(c_17357,plain,
    ( sP0(k2_tsep_1(sK8,sK6,sK7),sK8) = iProver_top
    | m1_pre_topc(k2_tsep_1(sK8,sK6,sK7),sK8) != iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17353])).

cnf(c_7837,plain,
    ( ~ m1_pre_topc(X0_54,sK8)
    | m1_pre_topc(k2_tsep_1(sK8,sK6,X0_54),sK8)
    | ~ m1_pre_topc(sK6,sK8)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK8)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_3217])).

cnf(c_8060,plain,
    ( m1_pre_topc(k2_tsep_1(sK8,sK6,sK7),sK8)
    | ~ m1_pre_topc(sK7,sK8)
    | ~ m1_pre_topc(sK6,sK8)
    | v2_struct_0(sK8)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_7837])).

cnf(c_8061,plain,
    ( m1_pre_topc(k2_tsep_1(sK8,sK6,sK7),sK8) = iProver_top
    | m1_pre_topc(sK7,sK8) != iProver_top
    | m1_pre_topc(sK6,sK8) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8060])).

cnf(c_46,plain,
    ( m1_pre_topc(sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_143933,c_17357,c_8061,c_4827,c_46,c_45,c_44,c_43,c_41,c_39,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:56:41 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.76/3.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.76/3.99  
% 27.76/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.76/3.99  
% 27.76/3.99  ------  iProver source info
% 27.76/3.99  
% 27.76/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.76/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.76/3.99  git: non_committed_changes: false
% 27.76/3.99  git: last_make_outside_of_git: false
% 27.76/3.99  
% 27.76/3.99  ------ 
% 27.76/3.99  ------ Parsing...
% 27.76/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  ------ Proving...
% 27.76/3.99  ------ Problem Properties 
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  clauses                                 32
% 27.76/3.99  conjectures                             11
% 27.76/3.99  EPR                                     13
% 27.76/3.99  Horn                                    23
% 27.76/3.99  unary                                   11
% 27.76/3.99  binary                                  2
% 27.76/3.99  lits                                    109
% 27.76/3.99  lits eq                                 7
% 27.76/3.99  fd_pure                                 0
% 27.76/3.99  fd_pseudo                               0
% 27.76/3.99  fd_cond                                 0
% 27.76/3.99  fd_pseudo_cond                          1
% 27.76/3.99  AC symbols                              0
% 27.76/3.99  
% 27.76/3.99  ------ Input Options Time Limit: Unbounded
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing...
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 27.76/3.99  Current options:
% 27.76/3.99  ------ 
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing...
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing...
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 14 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 15 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.76/3.99  
% 27.76/3.99  ------ Proving...
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  % SZS status Theorem for theBenchmark.p
% 27.76/3.99  
% 27.76/3.99  % SZS output start CNFRefutation for theBenchmark.p
% 27.76/3.99  
% 27.76/3.99  fof(f8,conjecture,(
% 27.76/3.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 27.76/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/3.99  
% 27.76/3.99  fof(f9,negated_conjecture,(
% 27.76/3.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 27.76/3.99    inference(negated_conjecture,[],[f8])).
% 27.76/3.99  
% 27.76/3.99  fof(f20,plain,(
% 27.76/3.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 27.76/3.99    inference(ennf_transformation,[],[f9])).
% 27.76/3.99  
% 27.76/3.99  fof(f21,plain,(
% 27.76/3.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 27.76/3.99    inference(flattening,[],[f20])).
% 27.76/3.99  
% 27.76/3.99  fof(f38,plain,(
% 27.76/3.99    ( ! [X2,X0,X1] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k2_tsep_1(X0,X1,X2),sK8) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK8) & m1_pre_topc(X1,sK8) & m1_pre_topc(sK8,X0) & ~v2_struct_0(sK8))) )),
% 27.76/3.99    introduced(choice_axiom,[])).
% 27.76/3.99  
% 27.76/3.99  fof(f37,plain,(
% 27.76/3.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,sK7),X3) & ~r1_tsep_1(X1,sK7) & m1_pre_topc(sK7,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK7,X0) & ~v2_struct_0(sK7))) )),
% 27.76/3.99    introduced(choice_axiom,[])).
% 27.76/3.99  
% 27.76/3.99  fof(f36,plain,(
% 27.76/3.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,sK6,X2),X3) & ~r1_tsep_1(sK6,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(sK6,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 27.76/3.99    introduced(choice_axiom,[])).
% 27.76/3.99  
% 27.76/3.99  fof(f35,plain,(
% 27.76/3.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK5,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK5) & ~v2_struct_0(X1)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 27.76/3.99    introduced(choice_axiom,[])).
% 27.76/3.99  
% 27.76/3.99  fof(f39,plain,(
% 27.76/3.99    (((~m1_pre_topc(k2_tsep_1(sK5,sK6,sK7),sK8) & ~r1_tsep_1(sK6,sK7) & m1_pre_topc(sK7,sK8) & m1_pre_topc(sK6,sK8) & m1_pre_topc(sK8,sK5) & ~v2_struct_0(sK8)) & m1_pre_topc(sK7,sK5) & ~v2_struct_0(sK7)) & m1_pre_topc(sK6,sK5) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 27.76/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f21,f38,f37,f36,f35])).
% 27.76/3.99  
% 27.76/3.99  fof(f73,plain,(
% 27.76/3.99    m1_pre_topc(sK7,sK8)),
% 27.76/3.99    inference(cnf_transformation,[],[f39])).
% 27.76/3.99  
% 27.76/3.99  fof(f72,plain,(
% 27.76/3.99    m1_pre_topc(sK6,sK8)),
% 27.76/3.99    inference(cnf_transformation,[],[f39])).
% 27.76/3.99  
% 27.76/3.99  fof(f6,axiom,(
% 27.76/3.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 27.76/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/3.99  
% 27.76/3.99  fof(f16,plain,(
% 27.76/3.99    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 27.76/3.99    inference(ennf_transformation,[],[f6])).
% 27.76/3.99  
% 27.76/3.99  fof(f17,plain,(
% 27.76/3.99    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 27.76/3.99    inference(flattening,[],[f16])).
% 27.76/3.99  
% 27.76/3.99  fof(f60,plain,(
% 27.76/3.99    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.76/3.99    inference(cnf_transformation,[],[f17])).
% 27.76/3.99  
% 27.76/3.99  fof(f4,axiom,(
% 27.76/3.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 27.76/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/3.99  
% 27.76/3.99  fof(f13,plain,(
% 27.76/3.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 27.76/3.99    inference(ennf_transformation,[],[f4])).
% 27.76/3.99  
% 27.76/3.99  fof(f55,plain,(
% 27.76/3.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 27.76/3.99    inference(cnf_transformation,[],[f13])).
% 27.76/3.99  
% 27.76/3.99  fof(f3,axiom,(
% 27.76/3.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 27.76/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/3.99  
% 27.76/3.99  fof(f12,plain,(
% 27.76/3.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 27.76/3.99    inference(ennf_transformation,[],[f3])).
% 27.76/3.99  
% 27.76/3.99  fof(f54,plain,(
% 27.76/3.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 27.76/3.99    inference(cnf_transformation,[],[f12])).
% 27.76/3.99  
% 27.76/3.99  fof(f1,axiom,(
% 27.76/3.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 27.76/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/3.99  
% 27.76/3.99  fof(f10,plain,(
% 27.76/3.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 27.76/3.99    inference(ennf_transformation,[],[f1])).
% 27.76/3.99  
% 27.76/3.99  fof(f40,plain,(
% 27.76/3.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 27.76/3.99    inference(cnf_transformation,[],[f10])).
% 27.76/3.99  
% 27.76/3.99  fof(f65,plain,(
% 27.76/3.99    l1_pre_topc(sK5)),
% 27.76/3.99    inference(cnf_transformation,[],[f39])).
% 27.76/3.99  
% 27.76/3.99  fof(f66,plain,(
% 27.76/3.99    ~v2_struct_0(sK6)),
% 27.76/3.99    inference(cnf_transformation,[],[f39])).
% 27.76/3.99  
% 27.76/3.99  fof(f70,plain,(
% 27.76/3.99    ~v2_struct_0(sK8)),
% 27.76/3.99    inference(cnf_transformation,[],[f39])).
% 27.76/3.99  
% 27.76/3.99  fof(f71,plain,(
% 27.76/3.99    m1_pre_topc(sK8,sK5)),
% 27.76/3.99    inference(cnf_transformation,[],[f39])).
% 27.76/3.99  
% 27.76/3.99  fof(f5,axiom,(
% 27.76/3.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 27.76/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/3.99  
% 27.76/3.99  fof(f14,plain,(
% 27.76/3.99    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 27.76/3.99    inference(ennf_transformation,[],[f5])).
% 27.76/3.99  
% 27.76/3.99  fof(f15,plain,(
% 27.76/3.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 27.76/3.99    inference(flattening,[],[f14])).
% 27.76/3.99  
% 27.76/3.99  fof(f33,plain,(
% 27.76/3.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 27.76/3.99    inference(nnf_transformation,[],[f15])).
% 27.76/3.99  
% 27.76/3.99  fof(f56,plain,(
% 27.76/3.99    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.76/3.99    inference(cnf_transformation,[],[f33])).
% 27.76/3.99  
% 27.76/3.99  fof(f77,plain,(
% 27.76/3.99    ( ! [X2,X0,X1] : (u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.76/3.99    inference(equality_resolution,[],[f56])).
% 27.76/3.99  
% 27.76/3.99  fof(f74,plain,(
% 27.76/3.99    ~r1_tsep_1(sK6,sK7)),
% 27.76/3.99    inference(cnf_transformation,[],[f39])).
% 27.76/3.99  
% 27.76/3.99  fof(f68,plain,(
% 27.76/3.99    ~v2_struct_0(sK7)),
% 27.76/3.99    inference(cnf_transformation,[],[f39])).
% 27.76/3.99  
% 27.76/3.99  fof(f58,plain,(
% 27.76/3.99    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.76/3.99    inference(cnf_transformation,[],[f17])).
% 27.76/3.99  
% 27.76/3.99  fof(f59,plain,(
% 27.76/3.99    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.76/3.99    inference(cnf_transformation,[],[f17])).
% 27.76/3.99  
% 27.76/3.99  fof(f69,plain,(
% 27.76/3.99    m1_pre_topc(sK7,sK5)),
% 27.76/3.99    inference(cnf_transformation,[],[f39])).
% 27.76/3.99  
% 27.76/3.99  fof(f63,plain,(
% 27.76/3.99    ~v2_struct_0(sK5)),
% 27.76/3.99    inference(cnf_transformation,[],[f39])).
% 27.76/3.99  
% 27.76/3.99  fof(f67,plain,(
% 27.76/3.99    m1_pre_topc(sK6,sK5)),
% 27.76/3.99    inference(cnf_transformation,[],[f39])).
% 27.76/3.99  
% 27.76/3.99  fof(f22,plain,(
% 27.76/3.99    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 27.76/3.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 27.76/3.99  
% 27.76/3.99  fof(f26,plain,(
% 27.76/3.99    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 27.76/3.99    inference(nnf_transformation,[],[f22])).
% 27.76/3.99  
% 27.76/3.99  fof(f27,plain,(
% 27.76/3.99    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 27.76/3.99    inference(flattening,[],[f26])).
% 27.76/3.99  
% 27.76/3.99  fof(f28,plain,(
% 27.76/3.99    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 27.76/3.99    inference(rectify,[],[f27])).
% 27.76/3.99  
% 27.76/3.99  fof(f31,plain,(
% 27.76/3.99    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 27.76/3.99    introduced(choice_axiom,[])).
% 27.76/3.99  
% 27.76/3.99  fof(f30,plain,(
% 27.76/3.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 27.76/3.99    introduced(choice_axiom,[])).
% 27.76/3.99  
% 27.76/3.99  fof(f29,plain,(
% 27.76/3.99    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 27.76/3.99    introduced(choice_axiom,[])).
% 27.76/3.99  
% 27.76/3.99  fof(f32,plain,(
% 27.76/3.99    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 27.76/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f31,f30,f29])).
% 27.76/3.99  
% 27.76/3.99  fof(f43,plain,(
% 27.76/3.99    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 27.76/3.99    inference(cnf_transformation,[],[f32])).
% 27.76/3.99  
% 27.76/3.99  fof(f7,axiom,(
% 27.76/3.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 27.76/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/3.99  
% 27.76/3.99  fof(f18,plain,(
% 27.76/3.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.76/3.99    inference(ennf_transformation,[],[f7])).
% 27.76/3.99  
% 27.76/3.99  fof(f19,plain,(
% 27.76/3.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.76/3.99    inference(flattening,[],[f18])).
% 27.76/3.99  
% 27.76/3.99  fof(f34,plain,(
% 27.76/3.99    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.76/3.99    inference(nnf_transformation,[],[f19])).
% 27.76/3.99  
% 27.76/3.99  fof(f61,plain,(
% 27.76/3.99    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.76/3.99    inference(cnf_transformation,[],[f34])).
% 27.76/3.99  
% 27.76/3.99  fof(f64,plain,(
% 27.76/3.99    v2_pre_topc(sK5)),
% 27.76/3.99    inference(cnf_transformation,[],[f39])).
% 27.76/3.99  
% 27.76/3.99  fof(f75,plain,(
% 27.76/3.99    ~m1_pre_topc(k2_tsep_1(sK5,sK6,sK7),sK8)),
% 27.76/3.99    inference(cnf_transformation,[],[f39])).
% 27.76/3.99  
% 27.76/3.99  fof(f2,axiom,(
% 27.76/3.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 27.76/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/3.99  
% 27.76/3.99  fof(f11,plain,(
% 27.76/3.99    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 27.76/3.99    inference(ennf_transformation,[],[f2])).
% 27.76/3.99  
% 27.76/3.99  fof(f23,plain,(
% 27.76/3.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 27.76/3.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 27.76/3.99  
% 27.76/3.99  fof(f24,plain,(
% 27.76/3.99    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 27.76/3.99    inference(definition_folding,[],[f11,f23,f22])).
% 27.76/3.99  
% 27.76/3.99  fof(f53,plain,(
% 27.76/3.99    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 27.76/3.99    inference(cnf_transformation,[],[f24])).
% 27.76/3.99  
% 27.76/3.99  fof(f25,plain,(
% 27.76/3.99    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 27.76/3.99    inference(nnf_transformation,[],[f23])).
% 27.76/3.99  
% 27.76/3.99  fof(f41,plain,(
% 27.76/3.99    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 27.76/3.99    inference(cnf_transformation,[],[f25])).
% 27.76/3.99  
% 27.76/3.99  cnf(c_25,negated_conjecture,
% 27.76/3.99      ( m1_pre_topc(sK7,sK8) ),
% 27.76/3.99      inference(cnf_transformation,[],[f73]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_3213,negated_conjecture,
% 27.76/3.99      ( m1_pre_topc(sK7,sK8) ),
% 27.76/3.99      inference(subtyping,[status(esa)],[c_25]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_88727,plain,
% 27.76/3.99      ( m1_pre_topc(sK7,sK8) = iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_3213]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_26,negated_conjecture,
% 27.76/3.99      ( m1_pre_topc(sK6,sK8) ),
% 27.76/3.99      inference(cnf_transformation,[],[f72]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_3212,negated_conjecture,
% 27.76/3.99      ( m1_pre_topc(sK6,sK8) ),
% 27.76/3.99      inference(subtyping,[status(esa)],[c_26]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_88726,plain,
% 27.76/3.99      ( m1_pre_topc(sK6,sK8) = iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_3212]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_18,plain,
% 27.76/3.99      ( ~ m1_pre_topc(X0,X1)
% 27.76/3.99      | ~ m1_pre_topc(X2,X1)
% 27.76/3.99      | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
% 27.76/3.99      | v2_struct_0(X1)
% 27.76/3.99      | v2_struct_0(X0)
% 27.76/3.99      | v2_struct_0(X2)
% 27.76/3.99      | ~ l1_pre_topc(X1) ),
% 27.76/3.99      inference(cnf_transformation,[],[f60]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_3217,plain,
% 27.76/3.99      ( ~ m1_pre_topc(X0_54,X1_54)
% 27.76/3.99      | ~ m1_pre_topc(X2_54,X1_54)
% 27.76/3.99      | m1_pre_topc(k2_tsep_1(X1_54,X0_54,X2_54),X1_54)
% 27.76/3.99      | v2_struct_0(X0_54)
% 27.76/3.99      | v2_struct_0(X1_54)
% 27.76/3.99      | v2_struct_0(X2_54)
% 27.76/3.99      | ~ l1_pre_topc(X1_54) ),
% 27.76/3.99      inference(subtyping,[status(esa)],[c_18]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_88709,plain,
% 27.76/3.99      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 27.76/3.99      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 27.76/3.99      | m1_pre_topc(k2_tsep_1(X1_54,X0_54,X2_54),X1_54) = iProver_top
% 27.76/3.99      | v2_struct_0(X1_54) = iProver_top
% 27.76/3.99      | v2_struct_0(X0_54) = iProver_top
% 27.76/3.99      | v2_struct_0(X2_54) = iProver_top
% 27.76/3.99      | l1_pre_topc(X1_54) != iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_3217]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_15,plain,
% 27.76/3.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 27.76/3.99      inference(cnf_transformation,[],[f55]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_3218,plain,
% 27.76/3.99      ( ~ m1_pre_topc(X0_54,X1_54)
% 27.76/3.99      | ~ l1_pre_topc(X1_54)
% 27.76/3.99      | l1_pre_topc(X0_54) ),
% 27.76/3.99      inference(subtyping,[status(esa)],[c_15]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_88708,plain,
% 27.76/3.99      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 27.76/3.99      | l1_pre_topc(X1_54) != iProver_top
% 27.76/3.99      | l1_pre_topc(X0_54) = iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_3218]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_89248,plain,
% 27.76/3.99      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 27.76/3.99      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 27.76/3.99      | v2_struct_0(X1_54) = iProver_top
% 27.76/3.99      | v2_struct_0(X0_54) = iProver_top
% 27.76/3.99      | v2_struct_0(X2_54) = iProver_top
% 27.76/3.99      | l1_pre_topc(X1_54) != iProver_top
% 27.76/3.99      | l1_pre_topc(k2_tsep_1(X1_54,X0_54,X2_54)) = iProver_top ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_88709,c_88708]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_14,plain,
% 27.76/3.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 27.76/3.99      inference(cnf_transformation,[],[f54]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_0,plain,
% 27.76/3.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 27.76/3.99      inference(cnf_transformation,[],[f40]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_386,plain,
% 27.76/3.99      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 27.76/3.99      inference(resolution,[status(thm)],[c_14,c_0]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_3203,plain,
% 27.76/3.99      ( ~ l1_pre_topc(X0_54) | u1_struct_0(X0_54) = k2_struct_0(X0_54) ),
% 27.76/3.99      inference(subtyping,[status(esa)],[c_386]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_88712,plain,
% 27.76/3.99      ( u1_struct_0(X0_54) = k2_struct_0(X0_54)
% 27.76/3.99      | l1_pre_topc(X0_54) != iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_3203]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_89414,plain,
% 27.76/3.99      ( u1_struct_0(k2_tsep_1(X0_54,X1_54,X2_54)) = k2_struct_0(k2_tsep_1(X0_54,X1_54,X2_54))
% 27.76/3.99      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 27.76/3.99      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 27.76/3.99      | v2_struct_0(X0_54) = iProver_top
% 27.76/3.99      | v2_struct_0(X1_54) = iProver_top
% 27.76/3.99      | v2_struct_0(X2_54) = iProver_top
% 27.76/3.99      | l1_pre_topc(X0_54) != iProver_top ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_89248,c_88712]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_90040,plain,
% 27.76/3.99      ( u1_struct_0(k2_tsep_1(sK8,sK6,X0_54)) = k2_struct_0(k2_tsep_1(sK8,sK6,X0_54))
% 27.76/3.99      | m1_pre_topc(X0_54,sK8) != iProver_top
% 27.76/3.99      | v2_struct_0(X0_54) = iProver_top
% 27.76/3.99      | v2_struct_0(sK8) = iProver_top
% 27.76/3.99      | v2_struct_0(sK6) = iProver_top
% 27.76/3.99      | l1_pre_topc(sK8) != iProver_top ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_88726,c_89414]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_33,negated_conjecture,
% 27.76/3.99      ( l1_pre_topc(sK5) ),
% 27.76/3.99      inference(cnf_transformation,[],[f65]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_38,plain,
% 27.76/3.99      ( l1_pre_topc(sK5) = iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_32,negated_conjecture,
% 27.76/3.99      ( ~ v2_struct_0(sK6) ),
% 27.76/3.99      inference(cnf_transformation,[],[f66]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_39,plain,
% 27.76/3.99      ( v2_struct_0(sK6) != iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_28,negated_conjecture,
% 27.76/3.99      ( ~ v2_struct_0(sK8) ),
% 27.76/3.99      inference(cnf_transformation,[],[f70]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_43,plain,
% 27.76/3.99      ( v2_struct_0(sK8) != iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_27,negated_conjecture,
% 27.76/3.99      ( m1_pre_topc(sK8,sK5) ),
% 27.76/3.99      inference(cnf_transformation,[],[f71]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_44,plain,
% 27.76/3.99      ( m1_pre_topc(sK8,sK5) = iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_4826,plain,
% 27.76/3.99      ( ~ m1_pre_topc(sK8,sK5) | l1_pre_topc(sK8) | ~ l1_pre_topc(sK5) ),
% 27.76/3.99      inference(instantiation,[status(thm)],[c_3218]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_4827,plain,
% 27.76/3.99      ( m1_pre_topc(sK8,sK5) != iProver_top
% 27.76/3.99      | l1_pre_topc(sK8) = iProver_top
% 27.76/3.99      | l1_pre_topc(sK5) != iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_4826]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_32308,plain,
% 27.76/3.99      ( m1_pre_topc(sK6,sK8) = iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_3212]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_32293,plain,
% 27.76/3.99      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 27.76/3.99      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 27.76/3.99      | m1_pre_topc(k2_tsep_1(X1_54,X0_54,X2_54),X1_54) = iProver_top
% 27.76/3.99      | v2_struct_0(X1_54) = iProver_top
% 27.76/3.99      | v2_struct_0(X0_54) = iProver_top
% 27.76/3.99      | v2_struct_0(X2_54) = iProver_top
% 27.76/3.99      | l1_pre_topc(X1_54) != iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_3217]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_32292,plain,
% 27.76/3.99      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 27.76/3.99      | l1_pre_topc(X1_54) != iProver_top
% 27.76/3.99      | l1_pre_topc(X0_54) = iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_3218]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_32888,plain,
% 27.76/3.99      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 27.76/3.99      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 27.76/3.99      | v2_struct_0(X1_54) = iProver_top
% 27.76/3.99      | v2_struct_0(X0_54) = iProver_top
% 27.76/3.99      | v2_struct_0(X2_54) = iProver_top
% 27.76/3.99      | l1_pre_topc(X1_54) != iProver_top
% 27.76/3.99      | l1_pre_topc(k2_tsep_1(X1_54,X0_54,X2_54)) = iProver_top ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_32293,c_32292]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_32295,plain,
% 27.76/3.99      ( u1_struct_0(X0_54) = k2_struct_0(X0_54)
% 27.76/3.99      | l1_pre_topc(X0_54) != iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_3203]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_33452,plain,
% 27.76/3.99      ( u1_struct_0(k2_tsep_1(X0_54,X1_54,X2_54)) = k2_struct_0(k2_tsep_1(X0_54,X1_54,X2_54))
% 27.76/3.99      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 27.76/3.99      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 27.76/3.99      | v2_struct_0(X0_54) = iProver_top
% 27.76/3.99      | v2_struct_0(X1_54) = iProver_top
% 27.76/3.99      | v2_struct_0(X2_54) = iProver_top
% 27.76/3.99      | l1_pre_topc(X0_54) != iProver_top ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_32888,c_32295]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_34044,plain,
% 27.76/3.99      ( u1_struct_0(k2_tsep_1(sK8,sK6,X0_54)) = k2_struct_0(k2_tsep_1(sK8,sK6,X0_54))
% 27.76/3.99      | m1_pre_topc(X0_54,sK8) != iProver_top
% 27.76/3.99      | v2_struct_0(X0_54) = iProver_top
% 27.76/3.99      | v2_struct_0(sK8) = iProver_top
% 27.76/3.99      | v2_struct_0(sK6) = iProver_top
% 27.76/3.99      | l1_pre_topc(sK8) != iProver_top ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_32308,c_33452]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_90518,plain,
% 27.76/3.99      ( v2_struct_0(X0_54) = iProver_top
% 27.76/3.99      | m1_pre_topc(X0_54,sK8) != iProver_top
% 27.76/3.99      | u1_struct_0(k2_tsep_1(sK8,sK6,X0_54)) = k2_struct_0(k2_tsep_1(sK8,sK6,X0_54)) ),
% 27.76/3.99      inference(global_propositional_subsumption,
% 27.76/3.99                [status(thm)],
% 27.76/3.99                [c_90040,c_38,c_39,c_43,c_44,c_4827,c_34044]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_90519,plain,
% 27.76/3.99      ( u1_struct_0(k2_tsep_1(sK8,sK6,X0_54)) = k2_struct_0(k2_tsep_1(sK8,sK6,X0_54))
% 27.76/3.99      | m1_pre_topc(X0_54,sK8) != iProver_top
% 27.76/3.99      | v2_struct_0(X0_54) = iProver_top ),
% 27.76/3.99      inference(renaming,[status(thm)],[c_90518]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_90525,plain,
% 27.76/3.99      ( u1_struct_0(k2_tsep_1(sK8,sK6,sK7)) = k2_struct_0(k2_tsep_1(sK8,sK6,sK7))
% 27.76/3.99      | v2_struct_0(sK7) = iProver_top ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_88727,c_90519]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_17,plain,
% 27.76/3.99      ( r1_tsep_1(X0,X1)
% 27.76/3.99      | ~ m1_pre_topc(X0,X2)
% 27.76/3.99      | ~ m1_pre_topc(X1,X2)
% 27.76/3.99      | ~ m1_pre_topc(k2_tsep_1(X2,X0,X1),X2)
% 27.76/3.99      | v2_struct_0(X2)
% 27.76/3.99      | v2_struct_0(X0)
% 27.76/3.99      | v2_struct_0(X1)
% 27.76/3.99      | v2_struct_0(k2_tsep_1(X2,X0,X1))
% 27.76/3.99      | ~ v1_pre_topc(k2_tsep_1(X2,X0,X1))
% 27.76/3.99      | ~ l1_pre_topc(X2)
% 27.76/3.99      | u1_struct_0(k2_tsep_1(X2,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 27.76/3.99      inference(cnf_transformation,[],[f77]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_24,negated_conjecture,
% 27.76/3.99      ( ~ r1_tsep_1(sK6,sK7) ),
% 27.76/3.99      inference(cnf_transformation,[],[f74]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_498,plain,
% 27.76/3.99      ( ~ m1_pre_topc(X0,X1)
% 27.76/3.99      | ~ m1_pre_topc(X2,X1)
% 27.76/3.99      | ~ m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
% 27.76/3.99      | v2_struct_0(X0)
% 27.76/3.99      | v2_struct_0(X2)
% 27.76/3.99      | v2_struct_0(X1)
% 27.76/3.99      | v2_struct_0(k2_tsep_1(X1,X0,X2))
% 27.76/3.99      | ~ v1_pre_topc(k2_tsep_1(X1,X0,X2))
% 27.76/3.99      | ~ l1_pre_topc(X1)
% 27.76/3.99      | u1_struct_0(k2_tsep_1(X1,X0,X2)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X2))
% 27.76/3.99      | sK7 != X2
% 27.76/3.99      | sK6 != X0 ),
% 27.76/3.99      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_499,plain,
% 27.76/3.99      ( ~ m1_pre_topc(k2_tsep_1(X0,sK6,sK7),X0)
% 27.76/3.99      | ~ m1_pre_topc(sK7,X0)
% 27.76/3.99      | ~ m1_pre_topc(sK6,X0)
% 27.76/3.99      | v2_struct_0(X0)
% 27.76/3.99      | v2_struct_0(k2_tsep_1(X0,sK6,sK7))
% 27.76/3.99      | v2_struct_0(sK7)
% 27.76/3.99      | v2_struct_0(sK6)
% 27.76/3.99      | ~ v1_pre_topc(k2_tsep_1(X0,sK6,sK7))
% 27.76/3.99      | ~ l1_pre_topc(X0)
% 27.76/3.99      | u1_struct_0(k2_tsep_1(X0,sK6,sK7)) = k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) ),
% 27.76/3.99      inference(unflattening,[status(thm)],[c_498]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_30,negated_conjecture,
% 27.76/3.99      ( ~ v2_struct_0(sK7) ),
% 27.76/3.99      inference(cnf_transformation,[],[f68]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_503,plain,
% 27.76/3.99      ( ~ m1_pre_topc(k2_tsep_1(X0,sK6,sK7),X0)
% 27.76/3.99      | ~ m1_pre_topc(sK7,X0)
% 27.76/3.99      | ~ m1_pre_topc(sK6,X0)
% 27.76/3.99      | v2_struct_0(X0)
% 27.76/3.99      | v2_struct_0(k2_tsep_1(X0,sK6,sK7))
% 27.76/3.99      | ~ v1_pre_topc(k2_tsep_1(X0,sK6,sK7))
% 27.76/3.99      | ~ l1_pre_topc(X0)
% 27.76/3.99      | u1_struct_0(k2_tsep_1(X0,sK6,sK7)) = k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) ),
% 27.76/3.99      inference(global_propositional_subsumption,
% 27.76/3.99                [status(thm)],
% 27.76/3.99                [c_499,c_32,c_30]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_3198,plain,
% 27.76/3.99      ( ~ m1_pre_topc(k2_tsep_1(X0_54,sK6,sK7),X0_54)
% 27.76/3.99      | ~ m1_pre_topc(sK7,X0_54)
% 27.76/3.99      | ~ m1_pre_topc(sK6,X0_54)
% 27.76/3.99      | v2_struct_0(X0_54)
% 27.76/3.99      | v2_struct_0(k2_tsep_1(X0_54,sK6,sK7))
% 27.76/3.99      | ~ v1_pre_topc(k2_tsep_1(X0_54,sK6,sK7))
% 27.76/3.99      | ~ l1_pre_topc(X0_54)
% 27.76/3.99      | u1_struct_0(k2_tsep_1(X0_54,sK6,sK7)) = k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) ),
% 27.76/3.99      inference(subtyping,[status(esa)],[c_503]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_20,plain,
% 27.76/3.99      ( ~ m1_pre_topc(X0,X1)
% 27.76/3.99      | ~ m1_pre_topc(X2,X1)
% 27.76/3.99      | v2_struct_0(X1)
% 27.76/3.99      | v2_struct_0(X0)
% 27.76/3.99      | v2_struct_0(X2)
% 27.76/3.99      | ~ v2_struct_0(k2_tsep_1(X1,X0,X2))
% 27.76/3.99      | ~ l1_pre_topc(X1) ),
% 27.76/3.99      inference(cnf_transformation,[],[f58]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_3215,plain,
% 27.76/3.99      ( ~ m1_pre_topc(X0_54,X1_54)
% 27.76/3.99      | ~ m1_pre_topc(X2_54,X1_54)
% 27.76/3.99      | v2_struct_0(X0_54)
% 27.76/3.99      | v2_struct_0(X1_54)
% 27.76/3.99      | v2_struct_0(X2_54)
% 27.76/3.99      | ~ v2_struct_0(k2_tsep_1(X1_54,X0_54,X2_54))
% 27.76/3.99      | ~ l1_pre_topc(X1_54) ),
% 27.76/3.99      inference(subtyping,[status(esa)],[c_20]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_14147,plain,
% 27.76/3.99      ( ~ m1_pre_topc(sK7,X0_54)
% 27.76/3.99      | ~ m1_pre_topc(sK6,X0_54)
% 27.76/3.99      | v2_struct_0(X0_54)
% 27.76/3.99      | ~ v2_struct_0(k2_tsep_1(X0_54,sK6,sK7))
% 27.76/3.99      | v2_struct_0(sK7)
% 27.76/3.99      | v2_struct_0(sK6)
% 27.76/3.99      | ~ l1_pre_topc(X0_54) ),
% 27.76/3.99      inference(instantiation,[status(thm)],[c_3215]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_34725,plain,
% 27.76/3.99      ( ~ m1_pre_topc(X0_54,X1_54)
% 27.76/3.99      | m1_pre_topc(k2_tsep_1(X1_54,sK6,X0_54),X1_54)
% 27.76/3.99      | ~ m1_pre_topc(sK6,X1_54)
% 27.76/3.99      | v2_struct_0(X1_54)
% 27.76/3.99      | v2_struct_0(X0_54)
% 27.76/3.99      | v2_struct_0(sK6)
% 27.76/3.99      | ~ l1_pre_topc(X1_54) ),
% 27.76/3.99      inference(instantiation,[status(thm)],[c_3217]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_39135,plain,
% 27.76/3.99      ( m1_pre_topc(k2_tsep_1(X0_54,sK6,sK7),X0_54)
% 27.76/3.99      | ~ m1_pre_topc(sK7,X0_54)
% 27.76/3.99      | ~ m1_pre_topc(sK6,X0_54)
% 27.76/3.99      | v2_struct_0(X0_54)
% 27.76/3.99      | v2_struct_0(sK7)
% 27.76/3.99      | v2_struct_0(sK6)
% 27.76/3.99      | ~ l1_pre_topc(X0_54) ),
% 27.76/3.99      inference(instantiation,[status(thm)],[c_34725]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_19,plain,
% 27.76/3.99      ( ~ m1_pre_topc(X0,X1)
% 27.76/3.99      | ~ m1_pre_topc(X2,X1)
% 27.76/3.99      | v2_struct_0(X1)
% 27.76/3.99      | v2_struct_0(X0)
% 27.76/3.99      | v2_struct_0(X2)
% 27.76/3.99      | v1_pre_topc(k2_tsep_1(X1,X0,X2))
% 27.76/3.99      | ~ l1_pre_topc(X1) ),
% 27.76/3.99      inference(cnf_transformation,[],[f59]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_3216,plain,
% 27.76/3.99      ( ~ m1_pre_topc(X0_54,X1_54)
% 27.76/3.99      | ~ m1_pre_topc(X2_54,X1_54)
% 27.76/3.99      | v2_struct_0(X0_54)
% 27.76/3.99      | v2_struct_0(X1_54)
% 27.76/3.99      | v2_struct_0(X2_54)
% 27.76/3.99      | v1_pre_topc(k2_tsep_1(X1_54,X0_54,X2_54))
% 27.76/3.99      | ~ l1_pre_topc(X1_54) ),
% 27.76/3.99      inference(subtyping,[status(esa)],[c_19]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_58490,plain,
% 27.76/3.99      ( ~ m1_pre_topc(X0_54,X1_54)
% 27.76/3.99      | ~ m1_pre_topc(sK6,X1_54)
% 27.76/3.99      | v2_struct_0(X1_54)
% 27.76/3.99      | v2_struct_0(X0_54)
% 27.76/3.99      | v2_struct_0(sK6)
% 27.76/3.99      | v1_pre_topc(k2_tsep_1(X1_54,sK6,X0_54))
% 27.76/3.99      | ~ l1_pre_topc(X1_54) ),
% 27.76/3.99      inference(instantiation,[status(thm)],[c_3216]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_68681,plain,
% 27.76/3.99      ( ~ m1_pre_topc(sK7,X0_54)
% 27.76/3.99      | ~ m1_pre_topc(sK6,X0_54)
% 27.76/3.99      | v2_struct_0(X0_54)
% 27.76/3.99      | v2_struct_0(sK7)
% 27.76/3.99      | v2_struct_0(sK6)
% 27.76/3.99      | v1_pre_topc(k2_tsep_1(X0_54,sK6,sK7))
% 27.76/3.99      | ~ l1_pre_topc(X0_54) ),
% 27.76/3.99      inference(instantiation,[status(thm)],[c_58490]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_88417,plain,
% 27.76/3.99      ( ~ m1_pre_topc(sK7,X0_54)
% 27.76/3.99      | ~ m1_pre_topc(sK6,X0_54)
% 27.76/3.99      | v2_struct_0(X0_54)
% 27.76/3.99      | ~ l1_pre_topc(X0_54)
% 27.76/3.99      | u1_struct_0(k2_tsep_1(X0_54,sK6,sK7)) = k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) ),
% 27.76/3.99      inference(global_propositional_subsumption,
% 27.76/3.99                [status(thm)],
% 27.76/3.99                [c_3198,c_32,c_30,c_14147,c_39135,c_68681]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_88542,plain,
% 27.76/3.99      ( ~ m1_pre_topc(sK7,X0_54)
% 27.76/3.99      | ~ m1_pre_topc(sK6,X0_54)
% 27.76/3.99      | v2_struct_0(X0_54)
% 27.76/3.99      | ~ l1_pre_topc(X0_54)
% 27.76/3.99      | u1_struct_0(k2_tsep_1(X0_54,sK6,sK7)) = k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) ),
% 27.76/3.99      inference(global_propositional_subsumption,
% 27.76/3.99                [status(thm)],
% 27.76/3.99                [c_3198,c_88417]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_88701,plain,
% 27.76/3.99      ( u1_struct_0(k2_tsep_1(X0_54,sK6,sK7)) = k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7))
% 27.76/3.99      | m1_pre_topc(sK7,X0_54) != iProver_top
% 27.76/3.99      | m1_pre_topc(sK6,X0_54) != iProver_top
% 27.76/3.99      | v2_struct_0(X0_54) = iProver_top
% 27.76/3.99      | l1_pre_topc(X0_54) != iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_88542]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_88974,plain,
% 27.76/3.99      ( k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) = u1_struct_0(k2_tsep_1(sK8,sK6,sK7))
% 27.76/3.99      | m1_pre_topc(sK6,sK8) != iProver_top
% 27.76/3.99      | v2_struct_0(sK8) = iProver_top
% 27.76/3.99      | l1_pre_topc(sK8) != iProver_top ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_88727,c_88701]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_45,plain,
% 27.76/3.99      ( m1_pre_topc(sK6,sK8) = iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_89063,plain,
% 27.76/3.99      ( k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) = u1_struct_0(k2_tsep_1(sK8,sK6,sK7)) ),
% 27.76/3.99      inference(global_propositional_subsumption,
% 27.76/3.99                [status(thm)],
% 27.76/3.99                [c_88974,c_38,c_43,c_44,c_45,c_4827]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_29,negated_conjecture,
% 27.76/3.99      ( m1_pre_topc(sK7,sK5) ),
% 27.76/3.99      inference(cnf_transformation,[],[f69]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_3209,negated_conjecture,
% 27.76/3.99      ( m1_pre_topc(sK7,sK5) ),
% 27.76/3.99      inference(subtyping,[status(esa)],[c_29]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_88723,plain,
% 27.76/3.99      ( m1_pre_topc(sK7,sK5) = iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_3209]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_88947,plain,
% 27.76/3.99      ( k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) = u1_struct_0(k2_tsep_1(sK5,sK6,sK7))
% 27.76/3.99      | m1_pre_topc(sK6,sK5) != iProver_top
% 27.76/3.99      | v2_struct_0(sK5) = iProver_top
% 27.76/3.99      | l1_pre_topc(sK5) != iProver_top ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_88723,c_88701]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_35,negated_conjecture,
% 27.76/3.99      ( ~ v2_struct_0(sK5) ),
% 27.76/3.99      inference(cnf_transformation,[],[f63]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_36,plain,
% 27.76/3.99      ( v2_struct_0(sK5) != iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_31,negated_conjecture,
% 27.76/3.99      ( m1_pre_topc(sK6,sK5) ),
% 27.76/3.99      inference(cnf_transformation,[],[f67]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_40,plain,
% 27.76/3.99      ( m1_pre_topc(sK6,sK5) = iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_89055,plain,
% 27.76/3.99      ( k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) = u1_struct_0(k2_tsep_1(sK5,sK6,sK7)) ),
% 27.76/3.99      inference(global_propositional_subsumption,
% 27.76/3.99                [status(thm)],
% 27.76/3.99                [c_88947,c_36,c_38,c_40]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_89065,plain,
% 27.76/3.99      ( u1_struct_0(k2_tsep_1(sK8,sK6,sK7)) = u1_struct_0(k2_tsep_1(sK5,sK6,sK7)) ),
% 27.76/3.99      inference(light_normalisation,[status(thm)],[c_89063,c_89055]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_90550,plain,
% 27.76/3.99      ( u1_struct_0(k2_tsep_1(sK5,sK6,sK7)) = k2_struct_0(k2_tsep_1(sK8,sK6,sK7))
% 27.76/3.99      | v2_struct_0(sK7) = iProver_top ),
% 27.76/3.99      inference(demodulation,[status(thm)],[c_90525,c_89065]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_41,plain,
% 27.76/3.99      ( v2_struct_0(sK7) != iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_143903,plain,
% 27.76/3.99      ( u1_struct_0(k2_tsep_1(sK5,sK6,sK7)) = k2_struct_0(k2_tsep_1(sK8,sK6,sK7)) ),
% 27.76/3.99      inference(global_propositional_subsumption,
% 27.76/3.99                [status(thm)],
% 27.76/3.99                [c_90550,c_41]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_3207,negated_conjecture,
% 27.76/3.99      ( m1_pre_topc(sK6,sK5) ),
% 27.76/3.99      inference(subtyping,[status(esa)],[c_31]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_88721,plain,
% 27.76/3.99      ( m1_pre_topc(sK6,sK5) = iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_3207]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_90043,plain,
% 27.76/3.99      ( u1_struct_0(k2_tsep_1(sK5,sK6,X0_54)) = k2_struct_0(k2_tsep_1(sK5,sK6,X0_54))
% 27.76/3.99      | m1_pre_topc(X0_54,sK5) != iProver_top
% 27.76/3.99      | v2_struct_0(X0_54) = iProver_top
% 27.76/3.99      | v2_struct_0(sK6) = iProver_top
% 27.76/3.99      | v2_struct_0(sK5) = iProver_top
% 27.76/3.99      | l1_pre_topc(sK5) != iProver_top ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_88721,c_89414]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_32303,plain,
% 27.76/3.99      ( m1_pre_topc(sK6,sK5) = iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_3207]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_34047,plain,
% 27.76/3.99      ( u1_struct_0(k2_tsep_1(sK5,sK6,X0_54)) = k2_struct_0(k2_tsep_1(sK5,sK6,X0_54))
% 27.76/3.99      | m1_pre_topc(X0_54,sK5) != iProver_top
% 27.76/3.99      | v2_struct_0(X0_54) = iProver_top
% 27.76/3.99      | v2_struct_0(sK6) = iProver_top
% 27.76/3.99      | v2_struct_0(sK5) = iProver_top
% 27.76/3.99      | l1_pre_topc(sK5) != iProver_top ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_32303,c_33452]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_35912,plain,
% 27.76/3.99      ( v2_struct_0(X0_54) = iProver_top
% 27.76/3.99      | m1_pre_topc(X0_54,sK5) != iProver_top
% 27.76/3.99      | u1_struct_0(k2_tsep_1(sK5,sK6,X0_54)) = k2_struct_0(k2_tsep_1(sK5,sK6,X0_54)) ),
% 27.76/3.99      inference(global_propositional_subsumption,
% 27.76/3.99                [status(thm)],
% 27.76/3.99                [c_34047,c_36,c_38,c_39]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_35913,plain,
% 27.76/3.99      ( u1_struct_0(k2_tsep_1(sK5,sK6,X0_54)) = k2_struct_0(k2_tsep_1(sK5,sK6,X0_54))
% 27.76/3.99      | m1_pre_topc(X0_54,sK5) != iProver_top
% 27.76/3.99      | v2_struct_0(X0_54) = iProver_top ),
% 27.76/3.99      inference(renaming,[status(thm)],[c_35912]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_91887,plain,
% 27.76/3.99      ( v2_struct_0(X0_54) = iProver_top
% 27.76/3.99      | m1_pre_topc(X0_54,sK5) != iProver_top
% 27.76/3.99      | u1_struct_0(k2_tsep_1(sK5,sK6,X0_54)) = k2_struct_0(k2_tsep_1(sK5,sK6,X0_54)) ),
% 27.76/3.99      inference(global_propositional_subsumption,
% 27.76/3.99                [status(thm)],
% 27.76/3.99                [c_90043,c_36,c_38,c_39,c_34047]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_91888,plain,
% 27.76/3.99      ( u1_struct_0(k2_tsep_1(sK5,sK6,X0_54)) = k2_struct_0(k2_tsep_1(sK5,sK6,X0_54))
% 27.76/3.99      | m1_pre_topc(X0_54,sK5) != iProver_top
% 27.76/3.99      | v2_struct_0(X0_54) = iProver_top ),
% 27.76/3.99      inference(renaming,[status(thm)],[c_91887]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_91895,plain,
% 27.76/3.99      ( u1_struct_0(k2_tsep_1(sK5,sK6,sK7)) = k2_struct_0(k2_tsep_1(sK5,sK6,sK7))
% 27.76/3.99      | v2_struct_0(sK7) = iProver_top ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_88723,c_91888]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_32305,plain,
% 27.76/3.99      ( m1_pre_topc(sK7,sK5) = iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_3209]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_35922,plain,
% 27.76/3.99      ( u1_struct_0(k2_tsep_1(sK5,sK6,sK7)) = k2_struct_0(k2_tsep_1(sK5,sK6,sK7))
% 27.76/3.99      | v2_struct_0(sK7) = iProver_top ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_32305,c_35913]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_92079,plain,
% 27.76/3.99      ( u1_struct_0(k2_tsep_1(sK5,sK6,sK7)) = k2_struct_0(k2_tsep_1(sK5,sK6,sK7)) ),
% 27.76/3.99      inference(global_propositional_subsumption,
% 27.76/3.99                [status(thm)],
% 27.76/3.99                [c_91895,c_41,c_35922]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_143905,plain,
% 27.76/3.99      ( k2_struct_0(k2_tsep_1(sK5,sK6,sK7)) = k2_struct_0(k2_tsep_1(sK8,sK6,sK7)) ),
% 27.76/3.99      inference(light_normalisation,[status(thm)],[c_143903,c_92079]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_12,plain,
% 27.76/3.99      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~ sP0(X0,X1) ),
% 27.76/3.99      inference(cnf_transformation,[],[f43]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_3219,plain,
% 27.76/3.99      ( r1_tarski(k2_struct_0(X0_54),k2_struct_0(X1_54))
% 27.76/3.99      | ~ sP0(X0_54,X1_54) ),
% 27.76/3.99      inference(subtyping,[status(esa)],[c_12]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_88707,plain,
% 27.76/3.99      ( r1_tarski(k2_struct_0(X0_54),k2_struct_0(X1_54)) = iProver_top
% 27.76/3.99      | sP0(X0_54,X1_54) != iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_3219]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_143907,plain,
% 27.76/3.99      ( r1_tarski(k2_struct_0(k2_tsep_1(sK5,sK6,sK7)),k2_struct_0(X0_54)) = iProver_top
% 27.76/3.99      | sP0(k2_tsep_1(sK8,sK6,sK7),X0_54) != iProver_top ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_143905,c_88707]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_3211,negated_conjecture,
% 27.76/3.99      ( m1_pre_topc(sK8,sK5) ),
% 27.76/3.99      inference(subtyping,[status(esa)],[c_27]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_88725,plain,
% 27.76/3.99      ( m1_pre_topc(sK8,sK5) = iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_3211]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_89190,plain,
% 27.76/3.99      ( l1_pre_topc(sK8) = iProver_top
% 27.76/3.99      | l1_pre_topc(sK5) != iProver_top ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_88725,c_88708]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_89290,plain,
% 27.76/3.99      ( l1_pre_topc(sK8) = iProver_top ),
% 27.76/3.99      inference(global_propositional_subsumption,
% 27.76/3.99                [status(thm)],
% 27.76/3.99                [c_89190,c_38,c_44,c_4827]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_89344,plain,
% 27.76/3.99      ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_89290,c_88712]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_22,plain,
% 27.76/3.99      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 27.76/3.99      | ~ m1_pre_topc(X0,X2)
% 27.76/3.99      | ~ m1_pre_topc(X1,X2)
% 27.76/3.99      | m1_pre_topc(X0,X1)
% 27.76/3.99      | ~ v2_pre_topc(X2)
% 27.76/3.99      | ~ l1_pre_topc(X2) ),
% 27.76/3.99      inference(cnf_transformation,[],[f61]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_34,negated_conjecture,
% 27.76/3.99      ( v2_pre_topc(sK5) ),
% 27.76/3.99      inference(cnf_transformation,[],[f64]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_444,plain,
% 27.76/3.99      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 27.76/3.99      | ~ m1_pre_topc(X0,X2)
% 27.76/3.99      | ~ m1_pre_topc(X1,X2)
% 27.76/3.99      | m1_pre_topc(X0,X1)
% 27.76/3.99      | ~ l1_pre_topc(X2)
% 27.76/3.99      | sK5 != X2 ),
% 27.76/3.99      inference(resolution_lifted,[status(thm)],[c_22,c_34]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_445,plain,
% 27.76/3.99      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 27.76/3.99      | m1_pre_topc(X0,X1)
% 27.76/3.99      | ~ m1_pre_topc(X1,sK5)
% 27.76/3.99      | ~ m1_pre_topc(X0,sK5)
% 27.76/3.99      | ~ l1_pre_topc(sK5) ),
% 27.76/3.99      inference(unflattening,[status(thm)],[c_444]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_447,plain,
% 27.76/3.99      ( ~ m1_pre_topc(X0,sK5)
% 27.76/3.99      | ~ m1_pre_topc(X1,sK5)
% 27.76/3.99      | m1_pre_topc(X0,X1)
% 27.76/3.99      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
% 27.76/3.99      inference(global_propositional_subsumption,
% 27.76/3.99                [status(thm)],
% 27.76/3.99                [c_445,c_33]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_448,plain,
% 27.76/3.99      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 27.76/3.99      | m1_pre_topc(X0,X1)
% 27.76/3.99      | ~ m1_pre_topc(X1,sK5)
% 27.76/3.99      | ~ m1_pre_topc(X0,sK5) ),
% 27.76/3.99      inference(renaming,[status(thm)],[c_447]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_3200,plain,
% 27.76/3.99      ( ~ r1_tarski(u1_struct_0(X0_54),u1_struct_0(X1_54))
% 27.76/3.99      | m1_pre_topc(X0_54,X1_54)
% 27.76/3.99      | ~ m1_pre_topc(X1_54,sK5)
% 27.76/3.99      | ~ m1_pre_topc(X0_54,sK5) ),
% 27.76/3.99      inference(subtyping,[status(esa)],[c_448]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_88715,plain,
% 27.76/3.99      ( r1_tarski(u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 27.76/3.99      | m1_pre_topc(X0_54,X1_54) = iProver_top
% 27.76/3.99      | m1_pre_topc(X1_54,sK5) != iProver_top
% 27.76/3.99      | m1_pre_topc(X0_54,sK5) != iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_3200]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_89423,plain,
% 27.76/3.99      ( r1_tarski(u1_struct_0(X0_54),k2_struct_0(sK8)) != iProver_top
% 27.76/3.99      | m1_pre_topc(X0_54,sK8) = iProver_top
% 27.76/3.99      | m1_pre_topc(X0_54,sK5) != iProver_top
% 27.76/3.99      | m1_pre_topc(sK8,sK5) != iProver_top ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_89344,c_88715]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_32307,plain,
% 27.76/3.99      ( m1_pre_topc(sK8,sK5) = iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_3211]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_32848,plain,
% 27.76/3.99      ( l1_pre_topc(sK8) = iProver_top
% 27.76/3.99      | l1_pre_topc(sK5) != iProver_top ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_32307,c_32292]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_32973,plain,
% 27.76/3.99      ( l1_pre_topc(sK8) = iProver_top ),
% 27.76/3.99      inference(global_propositional_subsumption,
% 27.76/3.99                [status(thm)],
% 27.76/3.99                [c_32848,c_38,c_44,c_4827]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_32978,plain,
% 27.76/3.99      ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_32973,c_32295]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_32298,plain,
% 27.76/3.99      ( r1_tarski(u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 27.76/3.99      | m1_pre_topc(X0_54,X1_54) = iProver_top
% 27.76/3.99      | m1_pre_topc(X1_54,sK5) != iProver_top
% 27.76/3.99      | m1_pre_topc(X0_54,sK5) != iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_3200]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_33318,plain,
% 27.76/3.99      ( r1_tarski(u1_struct_0(X0_54),k2_struct_0(sK8)) != iProver_top
% 27.76/3.99      | m1_pre_topc(X0_54,sK8) = iProver_top
% 27.76/3.99      | m1_pre_topc(X0_54,sK5) != iProver_top
% 27.76/3.99      | m1_pre_topc(sK8,sK5) != iProver_top ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_32978,c_32298]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_89923,plain,
% 27.76/3.99      ( m1_pre_topc(X0_54,sK5) != iProver_top
% 27.76/3.99      | m1_pre_topc(X0_54,sK8) = iProver_top
% 27.76/3.99      | r1_tarski(u1_struct_0(X0_54),k2_struct_0(sK8)) != iProver_top ),
% 27.76/3.99      inference(global_propositional_subsumption,
% 27.76/3.99                [status(thm)],
% 27.76/3.99                [c_89423,c_44,c_33318]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_89924,plain,
% 27.76/3.99      ( r1_tarski(u1_struct_0(X0_54),k2_struct_0(sK8)) != iProver_top
% 27.76/3.99      | m1_pre_topc(X0_54,sK8) = iProver_top
% 27.76/3.99      | m1_pre_topc(X0_54,sK5) != iProver_top ),
% 27.76/3.99      inference(renaming,[status(thm)],[c_89923]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_92124,plain,
% 27.76/3.99      ( r1_tarski(k2_struct_0(k2_tsep_1(sK5,sK6,sK7)),k2_struct_0(sK8)) != iProver_top
% 27.76/3.99      | m1_pre_topc(k2_tsep_1(sK5,sK6,sK7),sK8) = iProver_top
% 27.76/3.99      | m1_pre_topc(k2_tsep_1(sK5,sK6,sK7),sK5) != iProver_top ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_92079,c_89924]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_42,plain,
% 27.76/3.99      ( m1_pre_topc(sK7,sK5) = iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_23,negated_conjecture,
% 27.76/3.99      ( ~ m1_pre_topc(k2_tsep_1(sK5,sK6,sK7),sK8) ),
% 27.76/3.99      inference(cnf_transformation,[],[f75]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_48,plain,
% 27.76/3.99      ( m1_pre_topc(k2_tsep_1(sK5,sK6,sK7),sK8) != iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_7763,plain,
% 27.76/3.99      ( ~ m1_pre_topc(X0_54,sK5)
% 27.76/3.99      | m1_pre_topc(k2_tsep_1(sK5,sK6,X0_54),sK5)
% 27.76/3.99      | ~ m1_pre_topc(sK6,sK5)
% 27.76/3.99      | v2_struct_0(X0_54)
% 27.76/3.99      | v2_struct_0(sK6)
% 27.76/3.99      | v2_struct_0(sK5)
% 27.76/3.99      | ~ l1_pre_topc(sK5) ),
% 27.76/3.99      inference(instantiation,[status(thm)],[c_3217]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_7895,plain,
% 27.76/3.99      ( m1_pre_topc(k2_tsep_1(sK5,sK6,sK7),sK5)
% 27.76/3.99      | ~ m1_pre_topc(sK7,sK5)
% 27.76/3.99      | ~ m1_pre_topc(sK6,sK5)
% 27.76/3.99      | v2_struct_0(sK7)
% 27.76/3.99      | v2_struct_0(sK6)
% 27.76/3.99      | v2_struct_0(sK5)
% 27.76/3.99      | ~ l1_pre_topc(sK5) ),
% 27.76/3.99      inference(instantiation,[status(thm)],[c_7763]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_7896,plain,
% 27.76/3.99      ( m1_pre_topc(k2_tsep_1(sK5,sK6,sK7),sK5) = iProver_top
% 27.76/3.99      | m1_pre_topc(sK7,sK5) != iProver_top
% 27.76/3.99      | m1_pre_topc(sK6,sK5) != iProver_top
% 27.76/3.99      | v2_struct_0(sK7) = iProver_top
% 27.76/3.99      | v2_struct_0(sK6) = iProver_top
% 27.76/3.99      | v2_struct_0(sK5) = iProver_top
% 27.76/3.99      | l1_pre_topc(sK5) != iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_7895]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_36147,plain,
% 27.76/3.99      ( u1_struct_0(k2_tsep_1(sK5,sK6,sK7)) = k2_struct_0(k2_tsep_1(sK5,sK6,sK7)) ),
% 27.76/3.99      inference(global_propositional_subsumption,
% 27.76/3.99                [status(thm)],
% 27.76/3.99                [c_35922,c_41]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_44030,plain,
% 27.76/3.99      ( m1_pre_topc(X0_54,sK5) != iProver_top
% 27.76/3.99      | m1_pre_topc(X0_54,sK8) = iProver_top
% 27.76/3.99      | r1_tarski(u1_struct_0(X0_54),k2_struct_0(sK8)) != iProver_top ),
% 27.76/3.99      inference(global_propositional_subsumption,
% 27.76/3.99                [status(thm)],
% 27.76/3.99                [c_33318,c_44]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_44031,plain,
% 27.76/3.99      ( r1_tarski(u1_struct_0(X0_54),k2_struct_0(sK8)) != iProver_top
% 27.76/3.99      | m1_pre_topc(X0_54,sK8) = iProver_top
% 27.76/3.99      | m1_pre_topc(X0_54,sK5) != iProver_top ),
% 27.76/3.99      inference(renaming,[status(thm)],[c_44030]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_44043,plain,
% 27.76/3.99      ( r1_tarski(k2_struct_0(k2_tsep_1(sK5,sK6,sK7)),k2_struct_0(sK8)) != iProver_top
% 27.76/3.99      | m1_pre_topc(k2_tsep_1(sK5,sK6,sK7),sK8) = iProver_top
% 27.76/3.99      | m1_pre_topc(k2_tsep_1(sK5,sK6,sK7),sK5) != iProver_top ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_36147,c_44031]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_112639,plain,
% 27.76/3.99      ( r1_tarski(k2_struct_0(k2_tsep_1(sK5,sK6,sK7)),k2_struct_0(sK8)) != iProver_top ),
% 27.76/3.99      inference(global_propositional_subsumption,
% 27.76/3.99                [status(thm)],
% 27.76/3.99                [c_92124,c_36,c_38,c_39,c_40,c_41,c_42,c_48,c_7896,
% 27.76/3.99                 c_44043]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_143933,plain,
% 27.76/3.99      ( sP0(k2_tsep_1(sK8,sK6,sK7),sK8) != iProver_top ),
% 27.76/3.99      inference(superposition,[status(thm)],[c_143907,c_112639]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_13,plain,
% 27.76/3.99      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 27.76/3.99      inference(cnf_transformation,[],[f53]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_2,plain,
% 27.76/3.99      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 27.76/3.99      inference(cnf_transformation,[],[f41]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_400,plain,
% 27.76/3.99      ( sP0(X0,X1)
% 27.76/3.99      | ~ m1_pre_topc(X0,X1)
% 27.76/3.99      | ~ l1_pre_topc(X1)
% 27.76/3.99      | ~ l1_pre_topc(X0) ),
% 27.76/3.99      inference(resolution,[status(thm)],[c_13,c_2]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_404,plain,
% 27.76/3.99      ( ~ l1_pre_topc(X1) | ~ m1_pre_topc(X0,X1) | sP0(X0,X1) ),
% 27.76/3.99      inference(global_propositional_subsumption,
% 27.76/3.99                [status(thm)],
% 27.76/3.99                [c_400,c_15]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_405,plain,
% 27.76/3.99      ( sP0(X0,X1) | ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) ),
% 27.76/3.99      inference(renaming,[status(thm)],[c_404]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_3202,plain,
% 27.76/3.99      ( sP0(X0_54,X1_54)
% 27.76/3.99      | ~ m1_pre_topc(X0_54,X1_54)
% 27.76/3.99      | ~ l1_pre_topc(X1_54) ),
% 27.76/3.99      inference(subtyping,[status(esa)],[c_405]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_17353,plain,
% 27.76/3.99      ( sP0(k2_tsep_1(sK8,sK6,sK7),sK8)
% 27.76/3.99      | ~ m1_pre_topc(k2_tsep_1(sK8,sK6,sK7),sK8)
% 27.76/3.99      | ~ l1_pre_topc(sK8) ),
% 27.76/3.99      inference(instantiation,[status(thm)],[c_3202]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_17357,plain,
% 27.76/3.99      ( sP0(k2_tsep_1(sK8,sK6,sK7),sK8) = iProver_top
% 27.76/3.99      | m1_pre_topc(k2_tsep_1(sK8,sK6,sK7),sK8) != iProver_top
% 27.76/3.99      | l1_pre_topc(sK8) != iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_17353]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_7837,plain,
% 27.76/3.99      ( ~ m1_pre_topc(X0_54,sK8)
% 27.76/3.99      | m1_pre_topc(k2_tsep_1(sK8,sK6,X0_54),sK8)
% 27.76/3.99      | ~ m1_pre_topc(sK6,sK8)
% 27.76/3.99      | v2_struct_0(X0_54)
% 27.76/3.99      | v2_struct_0(sK8)
% 27.76/3.99      | v2_struct_0(sK6)
% 27.76/3.99      | ~ l1_pre_topc(sK8) ),
% 27.76/3.99      inference(instantiation,[status(thm)],[c_3217]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_8060,plain,
% 27.76/3.99      ( m1_pre_topc(k2_tsep_1(sK8,sK6,sK7),sK8)
% 27.76/3.99      | ~ m1_pre_topc(sK7,sK8)
% 27.76/3.99      | ~ m1_pre_topc(sK6,sK8)
% 27.76/3.99      | v2_struct_0(sK8)
% 27.76/3.99      | v2_struct_0(sK7)
% 27.76/3.99      | v2_struct_0(sK6)
% 27.76/3.99      | ~ l1_pre_topc(sK8) ),
% 27.76/3.99      inference(instantiation,[status(thm)],[c_7837]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_8061,plain,
% 27.76/3.99      ( m1_pre_topc(k2_tsep_1(sK8,sK6,sK7),sK8) = iProver_top
% 27.76/3.99      | m1_pre_topc(sK7,sK8) != iProver_top
% 27.76/3.99      | m1_pre_topc(sK6,sK8) != iProver_top
% 27.76/3.99      | v2_struct_0(sK8) = iProver_top
% 27.76/3.99      | v2_struct_0(sK7) = iProver_top
% 27.76/3.99      | v2_struct_0(sK6) = iProver_top
% 27.76/3.99      | l1_pre_topc(sK8) != iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_8060]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(c_46,plain,
% 27.76/3.99      ( m1_pre_topc(sK7,sK8) = iProver_top ),
% 27.76/3.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 27.76/3.99  
% 27.76/3.99  cnf(contradiction,plain,
% 27.76/3.99      ( $false ),
% 27.76/3.99      inference(minisat,
% 27.76/3.99                [status(thm)],
% 27.76/3.99                [c_143933,c_17357,c_8061,c_4827,c_46,c_45,c_44,c_43,c_41,
% 27.76/3.99                 c_39,c_38]) ).
% 27.76/3.99  
% 27.76/3.99  
% 27.76/3.99  % SZS output end CNFRefutation for theBenchmark.p
% 27.76/3.99  
% 27.76/3.99  ------                               Statistics
% 27.76/3.99  
% 27.76/3.99  ------ Selected
% 27.76/3.99  
% 27.76/3.99  total_time:                             3.397
% 27.76/3.99  
%------------------------------------------------------------------------------
