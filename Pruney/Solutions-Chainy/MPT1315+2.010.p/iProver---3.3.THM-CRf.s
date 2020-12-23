%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:45 EST 2020

% Result     : Theorem 7.26s
% Output     : CNFRefutation 7.26s
% Verified   : 
% Statistics : Number of formulae       :  156 (1391 expanded)
%              Number of clauses        :   88 ( 431 expanded)
%              Number of leaves         :   21 ( 427 expanded)
%              Depth                    :   20
%              Number of atoms          :  562 (6765 expanded)
%              Number of equality atoms :  203 (1407 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v4_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f44,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v4_pre_topc(X3,X2)
          & X1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ~ v4_pre_topc(sK9,X2)
        & sK9 = X1
        & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ v4_pre_topc(X3,X2)
              & X1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
          & v4_pre_topc(X1,X0)
          & m1_pre_topc(X2,X0) )
     => ( ? [X3] :
            ( ~ v4_pre_topc(X3,sK8)
            & X1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8))) )
        & v4_pre_topc(X1,X0)
        & m1_pre_topc(sK8,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ v4_pre_topc(X3,X2)
                & sK7 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
            & v4_pre_topc(sK7,X0)
            & m1_pre_topc(X2,X0) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v4_pre_topc(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
                & v4_pre_topc(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,sK6)
              & m1_pre_topc(X2,sK6) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ~ v4_pre_topc(sK9,sK8)
    & sK7 = sK9
    & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    & v4_pre_topc(sK7,sK6)
    & m1_pre_topc(sK8,sK6)
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f24,f44,f43,f42,f41])).

fof(f75,plain,(
    m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f73,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v4_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2
        & v4_pre_topc(sK5(X0,X1,X2),X0)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v4_pre_topc(sK5(X0,X1,X2),X0)
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f8,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
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

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f19,f26,f25])).

fof(f66,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f54,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

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
    inference(nnf_transformation,[],[f25])).

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

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    sK7 = sK9 ),
    inference(cnf_transformation,[],[f45])).

fof(f83,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(definition_unfolding,[],[f74,f78])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f50])).

fof(f79,plain,(
    ~ v4_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f82,plain,(
    v4_pre_topc(sK9,sK6) ),
    inference(definition_unfolding,[],[f76,f78])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1075,plain,
    ( m1_pre_topc(sK8,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1083,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2294,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1075,c_1083])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_32,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1588,plain,
    ( ~ l1_pre_topc(sK6)
    | l1_pre_topc(sK8) ),
    inference(resolution,[status(thm)],[c_21,c_29])).

cnf(c_1589,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1588])).

cnf(c_2405,plain,
    ( l1_pre_topc(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2294,c_32,c_1589])).

cnf(c_20,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1084,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2410,plain,
    ( l1_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2405,c_1084])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1098,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2542,plain,
    ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(superposition,[status(thm)],[c_2410,c_1098])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1077,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1099,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1647,plain,
    ( r1_tarski(sK9,u1_struct_0(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1077,c_1099])).

cnf(c_2545,plain,
    ( r1_tarski(sK9,k2_struct_0(sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2542,c_1647])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_221,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_222,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_221])).

cnf(c_280,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_1,c_222])).

cnf(c_1072,plain,
    ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_280])).

cnf(c_9029,plain,
    ( k9_subset_1(k2_struct_0(sK8),sK9,X0) = k9_subset_1(k2_struct_0(sK8),X0,sK9) ),
    inference(superposition,[status(thm)],[c_2545,c_1072])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_282,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_222])).

cnf(c_1070,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_5754,plain,
    ( k9_subset_1(k2_struct_0(sK8),X0,sK9) = k1_setfam_1(k2_tarski(X0,sK9)) ),
    inference(superposition,[status(thm)],[c_2545,c_1070])).

cnf(c_9062,plain,
    ( k9_subset_1(k2_struct_0(sK8),sK9,X0) = k1_setfam_1(k2_tarski(X0,sK9)) ),
    inference(light_normalisation,[status(thm)],[c_9029,c_5754])).

cnf(c_22,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1082,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4188,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)),sK8) = iProver_top
    | m1_pre_topc(sK8,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k9_subset_1(k2_struct_0(sK8),X0,k2_struct_0(sK8)),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2542,c_1082])).

cnf(c_4209,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(k9_subset_1(k2_struct_0(sK8),X0,k2_struct_0(sK8)),sK8) = iProver_top
    | m1_pre_topc(sK8,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k9_subset_1(k2_struct_0(sK8),X0,k2_struct_0(sK8)),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4188,c_2542])).

cnf(c_19259,plain,
    ( v4_pre_topc(k9_subset_1(k2_struct_0(sK8),sK9,k2_struct_0(sK8)),sK8) = iProver_top
    | v4_pre_topc(sK9,X0) != iProver_top
    | m1_pre_topc(sK8,X0) != iProver_top
    | m1_subset_1(k1_setfam_1(k2_tarski(k2_struct_0(sK8),sK9)),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9062,c_4209])).

cnf(c_19,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1085,plain,
    ( sP1(X0,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1096,plain,
    ( sP1(X0,X1) != iProver_top
    | sP0(X1,X0) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2402,plain,
    ( sP0(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1085,c_1096])).

cnf(c_1948,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_8,c_19])).

cnf(c_2154,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X0,X1)
    | sP0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1948,c_21])).

cnf(c_2155,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_2154])).

cnf(c_2156,plain,
    ( sP0(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2155])).

cnf(c_8717,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | sP0(X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2402,c_2156])).

cnf(c_8718,plain,
    ( sP0(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_8717])).

cnf(c_8724,plain,
    ( sP0(sK8,sK6) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1075,c_8718])).

cnf(c_34,plain,
    ( m1_pre_topc(sK8,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1396,plain,
    ( ~ sP1(sK6,sK8)
    | sP0(sK8,sK6)
    | ~ m1_pre_topc(sK8,sK6) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1397,plain,
    ( sP1(sK6,sK8) != iProver_top
    | sP0(sK8,sK6) = iProver_top
    | m1_pre_topc(sK8,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1396])).

cnf(c_1640,plain,
    ( sP1(sK6,sK8)
    | ~ l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1641,plain,
    ( sP1(sK6,sK8) = iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1640])).

cnf(c_8727,plain,
    ( sP0(sK8,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8724,c_32,c_34,c_1397,c_1589,c_1641])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1086,plain,
    ( sP0(X0,X1) != iProver_top
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5752,plain,
    ( k9_subset_1(k2_struct_0(X0),X1,k2_struct_0(X2)) = k1_setfam_1(k2_tarski(X1,k2_struct_0(X2)))
    | sP0(X2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1086,c_1070])).

cnf(c_10858,plain,
    ( k9_subset_1(k2_struct_0(sK6),X0,k2_struct_0(sK8)) = k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))) ),
    inference(superposition,[status(thm)],[c_8727,c_5752])).

cnf(c_1073,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1481,plain,
    ( l1_struct_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1073,c_1084])).

cnf(c_1571,plain,
    ( u1_struct_0(sK6) = k2_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_1481,c_1098])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1074,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1648,plain,
    ( r1_tarski(sK9,u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1074,c_1099])).

cnf(c_1920,plain,
    ( r1_tarski(sK9,k2_struct_0(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1571,c_1648])).

cnf(c_9028,plain,
    ( k9_subset_1(k2_struct_0(sK6),sK9,X0) = k9_subset_1(k2_struct_0(sK6),X0,sK9) ),
    inference(superposition,[status(thm)],[c_1920,c_1072])).

cnf(c_5753,plain,
    ( k9_subset_1(k2_struct_0(sK6),X0,sK9) = k1_setfam_1(k2_tarski(X0,sK9)) ),
    inference(superposition,[status(thm)],[c_1920,c_1070])).

cnf(c_9065,plain,
    ( k9_subset_1(k2_struct_0(sK6),sK9,X0) = k1_setfam_1(k2_tarski(X0,sK9)) ),
    inference(light_normalisation,[status(thm)],[c_9028,c_5753])).

cnf(c_11330,plain,
    ( k1_setfam_1(k2_tarski(k2_struct_0(sK8),sK9)) = k1_setfam_1(k2_tarski(sK9,k2_struct_0(sK8))) ),
    inference(superposition,[status(thm)],[c_10858,c_9065])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1101,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1770,plain,
    ( k1_setfam_1(k2_tarski(sK9,u1_struct_0(sK8))) = sK9 ),
    inference(superposition,[status(thm)],[c_1647,c_1101])).

cnf(c_2544,plain,
    ( k1_setfam_1(k2_tarski(sK9,k2_struct_0(sK8))) = sK9 ),
    inference(demodulation,[status(thm)],[c_2542,c_1770])).

cnf(c_11332,plain,
    ( k1_setfam_1(k2_tarski(k2_struct_0(sK8),sK9)) = sK9 ),
    inference(light_normalisation,[status(thm)],[c_11330,c_2544])).

cnf(c_19266,plain,
    ( v4_pre_topc(k9_subset_1(k2_struct_0(sK8),sK9,k2_struct_0(sK8)),sK8) = iProver_top
    | v4_pre_topc(sK9,X0) != iProver_top
    | m1_pre_topc(sK8,X0) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19259,c_11332])).

cnf(c_19267,plain,
    ( v4_pre_topc(k1_setfam_1(k2_tarski(k2_struct_0(sK8),sK9)),sK8) = iProver_top
    | v4_pre_topc(sK9,X0) != iProver_top
    | m1_pre_topc(sK8,X0) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19266,c_9062])).

cnf(c_19268,plain,
    ( v4_pre_topc(sK9,X0) != iProver_top
    | v4_pre_topc(sK9,sK8) = iProver_top
    | m1_pre_topc(sK8,X0) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19267,c_11332])).

cnf(c_19306,plain,
    ( v4_pre_topc(sK9,sK6) != iProver_top
    | v4_pre_topc(sK9,sK8) = iProver_top
    | m1_pre_topc(sK8,sK6) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_19268])).

cnf(c_2546,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2542,c_1077])).

cnf(c_26,negated_conjecture,
    ( ~ v4_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_37,plain,
    ( v4_pre_topc(sK9,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_28,negated_conjecture,
    ( v4_pre_topc(sK9,sK6) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_35,plain,
    ( v4_pre_topc(sK9,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_33,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19306,c_2546,c_37,c_35,c_34,c_33,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:01:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.26/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.26/1.47  
% 7.26/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.26/1.47  
% 7.26/1.47  ------  iProver source info
% 7.26/1.47  
% 7.26/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.26/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.26/1.47  git: non_committed_changes: false
% 7.26/1.47  git: last_make_outside_of_git: false
% 7.26/1.47  
% 7.26/1.47  ------ 
% 7.26/1.47  ------ Parsing...
% 7.26/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.26/1.47  
% 7.26/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.26/1.47  
% 7.26/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.26/1.47  
% 7.26/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.26/1.47  ------ Proving...
% 7.26/1.47  ------ Problem Properties 
% 7.26/1.47  
% 7.26/1.47  
% 7.26/1.47  clauses                                 32
% 7.26/1.47  conjectures                             6
% 7.26/1.47  EPR                                     9
% 7.26/1.47  Horn                                    28
% 7.26/1.47  unary                                   6
% 7.26/1.47  binary                                  9
% 7.26/1.47  lits                                    95
% 7.26/1.47  lits eq                                 8
% 7.26/1.47  fd_pure                                 0
% 7.26/1.47  fd_pseudo                               0
% 7.26/1.47  fd_cond                                 0
% 7.26/1.47  fd_pseudo_cond                          0
% 7.26/1.47  AC symbols                              0
% 7.26/1.47  
% 7.26/1.47  ------ Input Options Time Limit: Unbounded
% 7.26/1.47  
% 7.26/1.47  
% 7.26/1.47  ------ 
% 7.26/1.47  Current options:
% 7.26/1.47  ------ 
% 7.26/1.47  
% 7.26/1.47  
% 7.26/1.47  
% 7.26/1.47  
% 7.26/1.47  ------ Proving...
% 7.26/1.47  
% 7.26/1.47  
% 7.26/1.47  % SZS status Theorem for theBenchmark.p
% 7.26/1.47  
% 7.26/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.26/1.47  
% 7.26/1.47  fof(f12,conjecture,(
% 7.26/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 7.26/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.47  
% 7.26/1.47  fof(f13,negated_conjecture,(
% 7.26/1.47    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 7.26/1.47    inference(negated_conjecture,[],[f12])).
% 7.26/1.47  
% 7.26/1.47  fof(f23,plain,(
% 7.26/1.47    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v4_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.26/1.47    inference(ennf_transformation,[],[f13])).
% 7.26/1.47  
% 7.26/1.47  fof(f24,plain,(
% 7.26/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.26/1.47    inference(flattening,[],[f23])).
% 7.26/1.47  
% 7.26/1.47  fof(f44,plain,(
% 7.26/1.47    ( ! [X2,X1] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) => (~v4_pre_topc(sK9,X2) & sK9 = X1 & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X2))))) )),
% 7.26/1.47    introduced(choice_axiom,[])).
% 7.26/1.47  
% 7.26/1.47  fof(f43,plain,(
% 7.26/1.47    ( ! [X0,X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) => (? [X3] : (~v4_pre_topc(X3,sK8) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8)))) & v4_pre_topc(X1,X0) & m1_pre_topc(sK8,X0))) )),
% 7.26/1.47    introduced(choice_axiom,[])).
% 7.26/1.47  
% 7.26/1.47  fof(f42,plain,(
% 7.26/1.47    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & sK7 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(sK7,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.26/1.47    introduced(choice_axiom,[])).
% 7.26/1.47  
% 7.26/1.47  fof(f41,plain,(
% 7.26/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,sK6) & m1_pre_topc(X2,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6))),
% 7.26/1.47    introduced(choice_axiom,[])).
% 7.26/1.47  
% 7.26/1.47  fof(f45,plain,(
% 7.26/1.47    (((~v4_pre_topc(sK9,sK8) & sK7 = sK9 & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))) & v4_pre_topc(sK7,sK6) & m1_pre_topc(sK8,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6)),
% 7.26/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f24,f44,f43,f42,f41])).
% 7.26/1.47  
% 7.26/1.47  fof(f75,plain,(
% 7.26/1.47    m1_pre_topc(sK8,sK6)),
% 7.26/1.47    inference(cnf_transformation,[],[f45])).
% 7.26/1.47  
% 7.26/1.47  fof(f10,axiom,(
% 7.26/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.26/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.47  
% 7.26/1.47  fof(f21,plain,(
% 7.26/1.47    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.26/1.47    inference(ennf_transformation,[],[f10])).
% 7.26/1.47  
% 7.26/1.47  fof(f68,plain,(
% 7.26/1.47    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.26/1.47    inference(cnf_transformation,[],[f21])).
% 7.26/1.47  
% 7.26/1.47  fof(f73,plain,(
% 7.26/1.47    l1_pre_topc(sK6)),
% 7.26/1.47    inference(cnf_transformation,[],[f45])).
% 7.26/1.47  
% 7.26/1.47  fof(f9,axiom,(
% 7.26/1.47    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.26/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.47  
% 7.26/1.47  fof(f20,plain,(
% 7.26/1.47    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.26/1.47    inference(ennf_transformation,[],[f9])).
% 7.26/1.47  
% 7.26/1.47  fof(f67,plain,(
% 7.26/1.47    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.26/1.47    inference(cnf_transformation,[],[f20])).
% 7.26/1.47  
% 7.26/1.47  fof(f7,axiom,(
% 7.26/1.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.26/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.47  
% 7.26/1.47  fof(f18,plain,(
% 7.26/1.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.26/1.47    inference(ennf_transformation,[],[f7])).
% 7.26/1.47  
% 7.26/1.47  fof(f53,plain,(
% 7.26/1.47    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.26/1.47    inference(cnf_transformation,[],[f18])).
% 7.26/1.47  
% 7.26/1.47  fof(f77,plain,(
% 7.26/1.47    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))),
% 7.26/1.47    inference(cnf_transformation,[],[f45])).
% 7.26/1.47  
% 7.26/1.47  fof(f6,axiom,(
% 7.26/1.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.26/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.47  
% 7.26/1.47  fof(f28,plain,(
% 7.26/1.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.26/1.47    inference(nnf_transformation,[],[f6])).
% 7.26/1.47  
% 7.26/1.47  fof(f51,plain,(
% 7.26/1.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.26/1.47    inference(cnf_transformation,[],[f28])).
% 7.26/1.47  
% 7.26/1.47  fof(f2,axiom,(
% 7.26/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 7.26/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.47  
% 7.26/1.47  fof(f15,plain,(
% 7.26/1.47    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.26/1.47    inference(ennf_transformation,[],[f2])).
% 7.26/1.47  
% 7.26/1.47  fof(f47,plain,(
% 7.26/1.47    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.26/1.47    inference(cnf_transformation,[],[f15])).
% 7.26/1.47  
% 7.26/1.47  fof(f52,plain,(
% 7.26/1.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.26/1.47    inference(cnf_transformation,[],[f28])).
% 7.26/1.47  
% 7.26/1.47  fof(f4,axiom,(
% 7.26/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.26/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.47  
% 7.26/1.47  fof(f17,plain,(
% 7.26/1.47    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.26/1.47    inference(ennf_transformation,[],[f4])).
% 7.26/1.47  
% 7.26/1.47  fof(f49,plain,(
% 7.26/1.47    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.26/1.47    inference(cnf_transformation,[],[f17])).
% 7.26/1.47  
% 7.26/1.47  fof(f5,axiom,(
% 7.26/1.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.26/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.47  
% 7.26/1.47  fof(f50,plain,(
% 7.26/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.26/1.47    inference(cnf_transformation,[],[f5])).
% 7.26/1.47  
% 7.26/1.47  fof(f81,plain,(
% 7.26/1.47    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.26/1.47    inference(definition_unfolding,[],[f49,f50])).
% 7.26/1.47  
% 7.26/1.47  fof(f11,axiom,(
% 7.26/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 7.26/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.47  
% 7.26/1.47  fof(f22,plain,(
% 7.26/1.47    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.26/1.47    inference(ennf_transformation,[],[f11])).
% 7.26/1.47  
% 7.26/1.47  fof(f37,plain,(
% 7.26/1.47    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.26/1.47    inference(nnf_transformation,[],[f22])).
% 7.26/1.47  
% 7.26/1.47  fof(f38,plain,(
% 7.26/1.47    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v4_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.26/1.47    inference(rectify,[],[f37])).
% 7.26/1.47  
% 7.26/1.47  fof(f39,plain,(
% 7.26/1.47    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v4_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2 & v4_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.26/1.47    introduced(choice_axiom,[])).
% 7.26/1.47  
% 7.26/1.47  fof(f40,plain,(
% 7.26/1.47    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2 & v4_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.26/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).
% 7.26/1.47  
% 7.26/1.47  fof(f72,plain,(
% 7.26/1.47    ( ! [X2,X0,X3,X1] : (v4_pre_topc(X2,X1) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.26/1.47    inference(cnf_transformation,[],[f40])).
% 7.26/1.47  
% 7.26/1.47  fof(f85,plain,(
% 7.26/1.47    ( ! [X0,X3,X1] : (v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.26/1.47    inference(equality_resolution,[],[f72])).
% 7.26/1.47  
% 7.26/1.47  fof(f8,axiom,(
% 7.26/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 7.26/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.47  
% 7.26/1.47  fof(f19,plain,(
% 7.26/1.47    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.26/1.47    inference(ennf_transformation,[],[f8])).
% 7.26/1.47  
% 7.26/1.47  fof(f26,plain,(
% 7.26/1.47    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 7.26/1.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 7.26/1.47  
% 7.26/1.47  fof(f25,plain,(
% 7.26/1.47    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 7.26/1.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.26/1.47  
% 7.26/1.47  fof(f27,plain,(
% 7.26/1.47    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.26/1.47    inference(definition_folding,[],[f19,f26,f25])).
% 7.26/1.47  
% 7.26/1.47  fof(f66,plain,(
% 7.26/1.47    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.26/1.47    inference(cnf_transformation,[],[f27])).
% 7.26/1.47  
% 7.26/1.47  fof(f29,plain,(
% 7.26/1.47    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 7.26/1.47    inference(nnf_transformation,[],[f26])).
% 7.26/1.47  
% 7.26/1.47  fof(f54,plain,(
% 7.26/1.47    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 7.26/1.47    inference(cnf_transformation,[],[f29])).
% 7.26/1.47  
% 7.26/1.47  fof(f30,plain,(
% 7.26/1.47    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 7.26/1.47    inference(nnf_transformation,[],[f25])).
% 7.26/1.47  
% 7.26/1.47  fof(f31,plain,(
% 7.26/1.47    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 7.26/1.47    inference(flattening,[],[f30])).
% 7.26/1.47  
% 7.26/1.47  fof(f32,plain,(
% 7.26/1.47    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 7.26/1.47    inference(rectify,[],[f31])).
% 7.26/1.47  
% 7.26/1.47  fof(f35,plain,(
% 7.26/1.47    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 7.26/1.47    introduced(choice_axiom,[])).
% 7.26/1.47  
% 7.26/1.47  fof(f34,plain,(
% 7.26/1.47    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 7.26/1.47    introduced(choice_axiom,[])).
% 7.26/1.47  
% 7.26/1.47  fof(f33,plain,(
% 7.26/1.47    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.26/1.47    introduced(choice_axiom,[])).
% 7.26/1.47  
% 7.26/1.47  fof(f36,plain,(
% 7.26/1.47    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 7.26/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f35,f34,f33])).
% 7.26/1.47  
% 7.26/1.47  fof(f56,plain,(
% 7.26/1.47    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 7.26/1.47    inference(cnf_transformation,[],[f36])).
% 7.26/1.47  
% 7.26/1.47  fof(f74,plain,(
% 7.26/1.47    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 7.26/1.47    inference(cnf_transformation,[],[f45])).
% 7.26/1.47  
% 7.26/1.47  fof(f78,plain,(
% 7.26/1.47    sK7 = sK9),
% 7.26/1.47    inference(cnf_transformation,[],[f45])).
% 7.26/1.47  
% 7.26/1.47  fof(f83,plain,(
% 7.26/1.47    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6)))),
% 7.26/1.47    inference(definition_unfolding,[],[f74,f78])).
% 7.26/1.47  
% 7.26/1.47  fof(f1,axiom,(
% 7.26/1.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.26/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.47  
% 7.26/1.47  fof(f14,plain,(
% 7.26/1.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.26/1.47    inference(ennf_transformation,[],[f1])).
% 7.26/1.47  
% 7.26/1.47  fof(f46,plain,(
% 7.26/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.26/1.47    inference(cnf_transformation,[],[f14])).
% 7.26/1.47  
% 7.26/1.47  fof(f80,plain,(
% 7.26/1.47    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.26/1.47    inference(definition_unfolding,[],[f46,f50])).
% 7.26/1.47  
% 7.26/1.47  fof(f79,plain,(
% 7.26/1.47    ~v4_pre_topc(sK9,sK8)),
% 7.26/1.47    inference(cnf_transformation,[],[f45])).
% 7.26/1.47  
% 7.26/1.47  fof(f76,plain,(
% 7.26/1.47    v4_pre_topc(sK7,sK6)),
% 7.26/1.47    inference(cnf_transformation,[],[f45])).
% 7.26/1.47  
% 7.26/1.47  fof(f82,plain,(
% 7.26/1.47    v4_pre_topc(sK9,sK6)),
% 7.26/1.47    inference(definition_unfolding,[],[f76,f78])).
% 7.26/1.47  
% 7.26/1.47  cnf(c_29,negated_conjecture,
% 7.26/1.47      ( m1_pre_topc(sK8,sK6) ),
% 7.26/1.47      inference(cnf_transformation,[],[f75]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1075,plain,
% 7.26/1.47      ( m1_pre_topc(sK8,sK6) = iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_21,plain,
% 7.26/1.47      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.26/1.47      inference(cnf_transformation,[],[f68]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1083,plain,
% 7.26/1.47      ( m1_pre_topc(X0,X1) != iProver_top
% 7.26/1.47      | l1_pre_topc(X1) != iProver_top
% 7.26/1.47      | l1_pre_topc(X0) = iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_2294,plain,
% 7.26/1.47      ( l1_pre_topc(sK6) != iProver_top
% 7.26/1.47      | l1_pre_topc(sK8) = iProver_top ),
% 7.26/1.47      inference(superposition,[status(thm)],[c_1075,c_1083]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_31,negated_conjecture,
% 7.26/1.47      ( l1_pre_topc(sK6) ),
% 7.26/1.47      inference(cnf_transformation,[],[f73]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_32,plain,
% 7.26/1.47      ( l1_pre_topc(sK6) = iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1588,plain,
% 7.26/1.47      ( ~ l1_pre_topc(sK6) | l1_pre_topc(sK8) ),
% 7.26/1.47      inference(resolution,[status(thm)],[c_21,c_29]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1589,plain,
% 7.26/1.47      ( l1_pre_topc(sK6) != iProver_top
% 7.26/1.47      | l1_pre_topc(sK8) = iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_1588]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_2405,plain,
% 7.26/1.47      ( l1_pre_topc(sK8) = iProver_top ),
% 7.26/1.47      inference(global_propositional_subsumption,
% 7.26/1.47                [status(thm)],
% 7.26/1.47                [c_2294,c_32,c_1589]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_20,plain,
% 7.26/1.47      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.26/1.47      inference(cnf_transformation,[],[f67]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1084,plain,
% 7.26/1.47      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_2410,plain,
% 7.26/1.47      ( l1_struct_0(sK8) = iProver_top ),
% 7.26/1.47      inference(superposition,[status(thm)],[c_2405,c_1084]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_6,plain,
% 7.26/1.47      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.26/1.47      inference(cnf_transformation,[],[f53]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1098,plain,
% 7.26/1.47      ( u1_struct_0(X0) = k2_struct_0(X0)
% 7.26/1.47      | l1_struct_0(X0) != iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_2542,plain,
% 7.26/1.47      ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
% 7.26/1.47      inference(superposition,[status(thm)],[c_2410,c_1098]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_27,negated_conjecture,
% 7.26/1.47      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
% 7.26/1.47      inference(cnf_transformation,[],[f77]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1077,plain,
% 7.26/1.47      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_5,plain,
% 7.26/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.26/1.47      inference(cnf_transformation,[],[f51]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1099,plain,
% 7.26/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.26/1.47      | r1_tarski(X0,X1) = iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1647,plain,
% 7.26/1.47      ( r1_tarski(sK9,u1_struct_0(sK8)) = iProver_top ),
% 7.26/1.47      inference(superposition,[status(thm)],[c_1077,c_1099]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_2545,plain,
% 7.26/1.47      ( r1_tarski(sK9,k2_struct_0(sK8)) = iProver_top ),
% 7.26/1.47      inference(demodulation,[status(thm)],[c_2542,c_1647]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1,plain,
% 7.26/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.26/1.47      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 7.26/1.47      inference(cnf_transformation,[],[f47]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_4,plain,
% 7.26/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.26/1.47      inference(cnf_transformation,[],[f52]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_221,plain,
% 7.26/1.47      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.26/1.47      inference(prop_impl,[status(thm)],[c_4]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_222,plain,
% 7.26/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.26/1.47      inference(renaming,[status(thm)],[c_221]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_280,plain,
% 7.26/1.47      ( ~ r1_tarski(X0,X1)
% 7.26/1.47      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 7.26/1.47      inference(bin_hyper_res,[status(thm)],[c_1,c_222]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1072,plain,
% 7.26/1.47      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
% 7.26/1.47      | r1_tarski(X1,X0) != iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_280]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_9029,plain,
% 7.26/1.47      ( k9_subset_1(k2_struct_0(sK8),sK9,X0) = k9_subset_1(k2_struct_0(sK8),X0,sK9) ),
% 7.26/1.47      inference(superposition,[status(thm)],[c_2545,c_1072]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_3,plain,
% 7.26/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.26/1.47      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 7.26/1.47      inference(cnf_transformation,[],[f81]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_282,plain,
% 7.26/1.47      ( ~ r1_tarski(X0,X1)
% 7.26/1.47      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 7.26/1.47      inference(bin_hyper_res,[status(thm)],[c_3,c_222]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1070,plain,
% 7.26/1.47      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 7.26/1.47      | r1_tarski(X2,X0) != iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_5754,plain,
% 7.26/1.47      ( k9_subset_1(k2_struct_0(sK8),X0,sK9) = k1_setfam_1(k2_tarski(X0,sK9)) ),
% 7.26/1.47      inference(superposition,[status(thm)],[c_2545,c_1070]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_9062,plain,
% 7.26/1.47      ( k9_subset_1(k2_struct_0(sK8),sK9,X0) = k1_setfam_1(k2_tarski(X0,sK9)) ),
% 7.26/1.47      inference(light_normalisation,[status(thm)],[c_9029,c_5754]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_22,plain,
% 7.26/1.47      ( ~ v4_pre_topc(X0,X1)
% 7.26/1.47      | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
% 7.26/1.47      | ~ m1_pre_topc(X2,X1)
% 7.26/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.26/1.47      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
% 7.26/1.47      | ~ l1_pre_topc(X1) ),
% 7.26/1.47      inference(cnf_transformation,[],[f85]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1082,plain,
% 7.26/1.47      ( v4_pre_topc(X0,X1) != iProver_top
% 7.26/1.47      | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2) = iProver_top
% 7.26/1.47      | m1_pre_topc(X2,X1) != iProver_top
% 7.26/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.26/1.47      | m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 7.26/1.47      | l1_pre_topc(X1) != iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_4188,plain,
% 7.26/1.47      ( v4_pre_topc(X0,X1) != iProver_top
% 7.26/1.47      | v4_pre_topc(k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)),sK8) = iProver_top
% 7.26/1.47      | m1_pre_topc(sK8,X1) != iProver_top
% 7.26/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.26/1.47      | m1_subset_1(k9_subset_1(k2_struct_0(sK8),X0,k2_struct_0(sK8)),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
% 7.26/1.47      | l1_pre_topc(X1) != iProver_top ),
% 7.26/1.47      inference(superposition,[status(thm)],[c_2542,c_1082]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_4209,plain,
% 7.26/1.47      ( v4_pre_topc(X0,X1) != iProver_top
% 7.26/1.47      | v4_pre_topc(k9_subset_1(k2_struct_0(sK8),X0,k2_struct_0(sK8)),sK8) = iProver_top
% 7.26/1.47      | m1_pre_topc(sK8,X1) != iProver_top
% 7.26/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.26/1.47      | m1_subset_1(k9_subset_1(k2_struct_0(sK8),X0,k2_struct_0(sK8)),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
% 7.26/1.47      | l1_pre_topc(X1) != iProver_top ),
% 7.26/1.47      inference(light_normalisation,[status(thm)],[c_4188,c_2542]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_19259,plain,
% 7.26/1.47      ( v4_pre_topc(k9_subset_1(k2_struct_0(sK8),sK9,k2_struct_0(sK8)),sK8) = iProver_top
% 7.26/1.47      | v4_pre_topc(sK9,X0) != iProver_top
% 7.26/1.47      | m1_pre_topc(sK8,X0) != iProver_top
% 7.26/1.47      | m1_subset_1(k1_setfam_1(k2_tarski(k2_struct_0(sK8),sK9)),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
% 7.26/1.47      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.26/1.47      | l1_pre_topc(X0) != iProver_top ),
% 7.26/1.47      inference(superposition,[status(thm)],[c_9062,c_4209]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_19,plain,
% 7.26/1.47      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 7.26/1.47      inference(cnf_transformation,[],[f66]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1085,plain,
% 7.26/1.47      ( sP1(X0,X1) = iProver_top
% 7.26/1.47      | l1_pre_topc(X1) != iProver_top
% 7.26/1.47      | l1_pre_topc(X0) != iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_8,plain,
% 7.26/1.47      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 7.26/1.47      inference(cnf_transformation,[],[f54]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1096,plain,
% 7.26/1.47      ( sP1(X0,X1) != iProver_top
% 7.26/1.47      | sP0(X1,X0) = iProver_top
% 7.26/1.47      | m1_pre_topc(X1,X0) != iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_2402,plain,
% 7.26/1.47      ( sP0(X0,X1) = iProver_top
% 7.26/1.47      | m1_pre_topc(X0,X1) != iProver_top
% 7.26/1.47      | l1_pre_topc(X1) != iProver_top
% 7.26/1.47      | l1_pre_topc(X0) != iProver_top ),
% 7.26/1.47      inference(superposition,[status(thm)],[c_1085,c_1096]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1948,plain,
% 7.26/1.47      ( sP0(X0,X1)
% 7.26/1.47      | ~ m1_pre_topc(X0,X1)
% 7.26/1.47      | ~ l1_pre_topc(X1)
% 7.26/1.47      | ~ l1_pre_topc(X0) ),
% 7.26/1.47      inference(resolution,[status(thm)],[c_8,c_19]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_2154,plain,
% 7.26/1.47      ( ~ l1_pre_topc(X1) | ~ m1_pre_topc(X0,X1) | sP0(X0,X1) ),
% 7.26/1.47      inference(global_propositional_subsumption,
% 7.26/1.47                [status(thm)],
% 7.26/1.47                [c_1948,c_21]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_2155,plain,
% 7.26/1.47      ( sP0(X0,X1) | ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) ),
% 7.26/1.47      inference(renaming,[status(thm)],[c_2154]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_2156,plain,
% 7.26/1.47      ( sP0(X0,X1) = iProver_top
% 7.26/1.47      | m1_pre_topc(X0,X1) != iProver_top
% 7.26/1.47      | l1_pre_topc(X1) != iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_2155]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_8717,plain,
% 7.26/1.47      ( l1_pre_topc(X1) != iProver_top
% 7.26/1.47      | m1_pre_topc(X0,X1) != iProver_top
% 7.26/1.47      | sP0(X0,X1) = iProver_top ),
% 7.26/1.47      inference(global_propositional_subsumption,
% 7.26/1.47                [status(thm)],
% 7.26/1.47                [c_2402,c_2156]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_8718,plain,
% 7.26/1.47      ( sP0(X0,X1) = iProver_top
% 7.26/1.47      | m1_pre_topc(X0,X1) != iProver_top
% 7.26/1.47      | l1_pre_topc(X1) != iProver_top ),
% 7.26/1.47      inference(renaming,[status(thm)],[c_8717]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_8724,plain,
% 7.26/1.47      ( sP0(sK8,sK6) = iProver_top | l1_pre_topc(sK6) != iProver_top ),
% 7.26/1.47      inference(superposition,[status(thm)],[c_1075,c_8718]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_34,plain,
% 7.26/1.47      ( m1_pre_topc(sK8,sK6) = iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1396,plain,
% 7.26/1.47      ( ~ sP1(sK6,sK8) | sP0(sK8,sK6) | ~ m1_pre_topc(sK8,sK6) ),
% 7.26/1.47      inference(instantiation,[status(thm)],[c_8]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1397,plain,
% 7.26/1.47      ( sP1(sK6,sK8) != iProver_top
% 7.26/1.47      | sP0(sK8,sK6) = iProver_top
% 7.26/1.47      | m1_pre_topc(sK8,sK6) != iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_1396]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1640,plain,
% 7.26/1.47      ( sP1(sK6,sK8) | ~ l1_pre_topc(sK6) | ~ l1_pre_topc(sK8) ),
% 7.26/1.47      inference(instantiation,[status(thm)],[c_19]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1641,plain,
% 7.26/1.47      ( sP1(sK6,sK8) = iProver_top
% 7.26/1.47      | l1_pre_topc(sK6) != iProver_top
% 7.26/1.47      | l1_pre_topc(sK8) != iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_1640]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_8727,plain,
% 7.26/1.47      ( sP0(sK8,sK6) = iProver_top ),
% 7.26/1.47      inference(global_propositional_subsumption,
% 7.26/1.47                [status(thm)],
% 7.26/1.47                [c_8724,c_32,c_34,c_1397,c_1589,c_1641]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_18,plain,
% 7.26/1.47      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 7.26/1.47      inference(cnf_transformation,[],[f56]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1086,plain,
% 7.26/1.47      ( sP0(X0,X1) != iProver_top
% 7.26/1.47      | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) = iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_5752,plain,
% 7.26/1.47      ( k9_subset_1(k2_struct_0(X0),X1,k2_struct_0(X2)) = k1_setfam_1(k2_tarski(X1,k2_struct_0(X2)))
% 7.26/1.47      | sP0(X2,X0) != iProver_top ),
% 7.26/1.47      inference(superposition,[status(thm)],[c_1086,c_1070]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_10858,plain,
% 7.26/1.47      ( k9_subset_1(k2_struct_0(sK6),X0,k2_struct_0(sK8)) = k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))) ),
% 7.26/1.47      inference(superposition,[status(thm)],[c_8727,c_5752]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1073,plain,
% 7.26/1.47      ( l1_pre_topc(sK6) = iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1481,plain,
% 7.26/1.47      ( l1_struct_0(sK6) = iProver_top ),
% 7.26/1.47      inference(superposition,[status(thm)],[c_1073,c_1084]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1571,plain,
% 7.26/1.47      ( u1_struct_0(sK6) = k2_struct_0(sK6) ),
% 7.26/1.47      inference(superposition,[status(thm)],[c_1481,c_1098]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_30,negated_conjecture,
% 7.26/1.47      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 7.26/1.47      inference(cnf_transformation,[],[f83]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1074,plain,
% 7.26/1.47      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1648,plain,
% 7.26/1.47      ( r1_tarski(sK9,u1_struct_0(sK6)) = iProver_top ),
% 7.26/1.47      inference(superposition,[status(thm)],[c_1074,c_1099]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1920,plain,
% 7.26/1.47      ( r1_tarski(sK9,k2_struct_0(sK6)) = iProver_top ),
% 7.26/1.47      inference(demodulation,[status(thm)],[c_1571,c_1648]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_9028,plain,
% 7.26/1.47      ( k9_subset_1(k2_struct_0(sK6),sK9,X0) = k9_subset_1(k2_struct_0(sK6),X0,sK9) ),
% 7.26/1.47      inference(superposition,[status(thm)],[c_1920,c_1072]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_5753,plain,
% 7.26/1.47      ( k9_subset_1(k2_struct_0(sK6),X0,sK9) = k1_setfam_1(k2_tarski(X0,sK9)) ),
% 7.26/1.47      inference(superposition,[status(thm)],[c_1920,c_1070]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_9065,plain,
% 7.26/1.47      ( k9_subset_1(k2_struct_0(sK6),sK9,X0) = k1_setfam_1(k2_tarski(X0,sK9)) ),
% 7.26/1.47      inference(light_normalisation,[status(thm)],[c_9028,c_5753]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_11330,plain,
% 7.26/1.47      ( k1_setfam_1(k2_tarski(k2_struct_0(sK8),sK9)) = k1_setfam_1(k2_tarski(sK9,k2_struct_0(sK8))) ),
% 7.26/1.47      inference(superposition,[status(thm)],[c_10858,c_9065]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_0,plain,
% 7.26/1.47      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 7.26/1.47      inference(cnf_transformation,[],[f80]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1101,plain,
% 7.26/1.47      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 7.26/1.47      | r1_tarski(X0,X1) != iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_1770,plain,
% 7.26/1.47      ( k1_setfam_1(k2_tarski(sK9,u1_struct_0(sK8))) = sK9 ),
% 7.26/1.47      inference(superposition,[status(thm)],[c_1647,c_1101]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_2544,plain,
% 7.26/1.47      ( k1_setfam_1(k2_tarski(sK9,k2_struct_0(sK8))) = sK9 ),
% 7.26/1.47      inference(demodulation,[status(thm)],[c_2542,c_1770]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_11332,plain,
% 7.26/1.47      ( k1_setfam_1(k2_tarski(k2_struct_0(sK8),sK9)) = sK9 ),
% 7.26/1.47      inference(light_normalisation,[status(thm)],[c_11330,c_2544]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_19266,plain,
% 7.26/1.47      ( v4_pre_topc(k9_subset_1(k2_struct_0(sK8),sK9,k2_struct_0(sK8)),sK8) = iProver_top
% 7.26/1.47      | v4_pre_topc(sK9,X0) != iProver_top
% 7.26/1.47      | m1_pre_topc(sK8,X0) != iProver_top
% 7.26/1.47      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.26/1.47      | m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
% 7.26/1.47      | l1_pre_topc(X0) != iProver_top ),
% 7.26/1.47      inference(light_normalisation,[status(thm)],[c_19259,c_11332]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_19267,plain,
% 7.26/1.47      ( v4_pre_topc(k1_setfam_1(k2_tarski(k2_struct_0(sK8),sK9)),sK8) = iProver_top
% 7.26/1.47      | v4_pre_topc(sK9,X0) != iProver_top
% 7.26/1.47      | m1_pre_topc(sK8,X0) != iProver_top
% 7.26/1.47      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.26/1.47      | m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
% 7.26/1.47      | l1_pre_topc(X0) != iProver_top ),
% 7.26/1.47      inference(demodulation,[status(thm)],[c_19266,c_9062]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_19268,plain,
% 7.26/1.47      ( v4_pre_topc(sK9,X0) != iProver_top
% 7.26/1.47      | v4_pre_topc(sK9,sK8) = iProver_top
% 7.26/1.47      | m1_pre_topc(sK8,X0) != iProver_top
% 7.26/1.47      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.26/1.47      | m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
% 7.26/1.47      | l1_pre_topc(X0) != iProver_top ),
% 7.26/1.47      inference(light_normalisation,[status(thm)],[c_19267,c_11332]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_19306,plain,
% 7.26/1.47      ( v4_pre_topc(sK9,sK6) != iProver_top
% 7.26/1.47      | v4_pre_topc(sK9,sK8) = iProver_top
% 7.26/1.47      | m1_pre_topc(sK8,sK6) != iProver_top
% 7.26/1.47      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 7.26/1.47      | m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
% 7.26/1.47      | l1_pre_topc(sK6) != iProver_top ),
% 7.26/1.47      inference(instantiation,[status(thm)],[c_19268]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_2546,plain,
% 7.26/1.47      ( m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) = iProver_top ),
% 7.26/1.47      inference(demodulation,[status(thm)],[c_2542,c_1077]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_26,negated_conjecture,
% 7.26/1.47      ( ~ v4_pre_topc(sK9,sK8) ),
% 7.26/1.47      inference(cnf_transformation,[],[f79]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_37,plain,
% 7.26/1.47      ( v4_pre_topc(sK9,sK8) != iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_28,negated_conjecture,
% 7.26/1.47      ( v4_pre_topc(sK9,sK6) ),
% 7.26/1.47      inference(cnf_transformation,[],[f82]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_35,plain,
% 7.26/1.47      ( v4_pre_topc(sK9,sK6) = iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(c_33,plain,
% 7.26/1.47      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 7.26/1.47      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.26/1.47  
% 7.26/1.47  cnf(contradiction,plain,
% 7.26/1.47      ( $false ),
% 7.26/1.47      inference(minisat,
% 7.26/1.47                [status(thm)],
% 7.26/1.47                [c_19306,c_2546,c_37,c_35,c_34,c_33,c_32]) ).
% 7.26/1.47  
% 7.26/1.47  
% 7.26/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 7.26/1.47  
% 7.26/1.47  ------                               Statistics
% 7.26/1.47  
% 7.26/1.47  ------ Selected
% 7.26/1.47  
% 7.26/1.47  total_time:                             0.621
% 7.26/1.47  
%------------------------------------------------------------------------------
