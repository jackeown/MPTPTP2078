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
% DateTime   : Thu Dec  3 12:16:45 EST 2020

% Result     : Theorem 7.95s
% Output     : CNFRefutation 7.95s
% Verified   : 
% Statistics : Number of formulae       :  167 (1468 expanded)
%              Number of clauses        :   94 ( 430 expanded)
%              Number of leaves         :   21 ( 448 expanded)
%              Depth                    :   23
%              Number of atoms          :  624 (7970 expanded)
%              Number of equality atoms :  211 (1514 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f47,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v4_pre_topc(X3,X2)
          & X1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ~ v4_pre_topc(sK9,X2)
        & sK9 = X1
        & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f48,plain,
    ( ~ v4_pre_topc(sK9,sK8)
    & sK7 = sK9
    & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    & v4_pre_topc(sK7,sK6)
    & m1_pre_topc(sK8,sK6)
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f26,f47,f46,f45,f44])).

fof(f83,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f12,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v4_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2
        & v4_pre_topc(sK5(X0,X1,X2),X0)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f81,plain,(
    m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f27,plain,(
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

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f20,f28,f27])).

fof(f71,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f74,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f38,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f38,f37,f36])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f48])).

fof(f84,plain,(
    sK7 = sK9 ),
    inference(cnf_transformation,[],[f48])).

fof(f89,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(definition_unfolding,[],[f80,f84])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f54])).

fof(f85,plain,(
    ~ v4_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f88,plain,(
    v4_pre_topc(sK9,sK6) ),
    inference(definition_unfolding,[],[f82,f84])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4745,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_4765,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5128,plain,
    ( r1_tarski(sK9,u1_struct_0(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4745,c_4765])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_280,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_281,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_280])).

cnf(c_344,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_1,c_281])).

cnf(c_4739,plain,
    ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_8651,plain,
    ( k9_subset_1(u1_struct_0(sK8),sK9,X0) = k9_subset_1(u1_struct_0(sK8),X0,sK9) ),
    inference(superposition,[status(thm)],[c_5128,c_4739])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_345,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_281])).

cnf(c_4738,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_5549,plain,
    ( k9_subset_1(u1_struct_0(sK8),X0,sK9) = k1_setfam_1(k2_tarski(X0,sK9)) ),
    inference(superposition,[status(thm)],[c_5128,c_4738])).

cnf(c_8658,plain,
    ( k9_subset_1(u1_struct_0(sK8),sK9,X0) = k1_setfam_1(k2_tarski(X0,sK9)) ),
    inference(light_normalisation,[status(thm)],[c_8651,c_5549])).

cnf(c_4766,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_25,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_4750,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7517,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),u1_struct_0(X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4766,c_4750])).

cnf(c_28231,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)),sK8) = iProver_top
    | v4_pre_topc(sK9,X0) != iProver_top
    | m1_pre_topc(sK8,X0) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(k2_struct_0(sK8),sK9)),u1_struct_0(sK8)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8658,c_7517])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_4743,plain,
    ( m1_pre_topc(sK8,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_21,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_10,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_500,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_21,c_10])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_504,plain,
    ( ~ m1_pre_topc(X0,X1)
    | sP0(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_500,c_24])).

cnf(c_505,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_504])).

cnf(c_4737,plain,
    ( sP0(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_5616,plain,
    ( sP0(sK8,sK6) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4743,c_4737])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_35,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_967,plain,
    ( sP0(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK6 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_505,c_32])).

cnf(c_968,plain,
    ( sP0(sK8,sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_967])).

cnf(c_969,plain,
    ( sP0(sK8,sK6) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_968])).

cnf(c_5850,plain,
    ( sP0(sK8,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5616,c_35,c_969])).

cnf(c_20,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_4754,plain,
    ( sP0(X0,X1) != iProver_top
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_8650,plain,
    ( k9_subset_1(k2_struct_0(X0),k2_struct_0(X1),X2) = k9_subset_1(k2_struct_0(X0),X2,k2_struct_0(X1))
    | sP0(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4754,c_4739])).

cnf(c_9299,plain,
    ( k9_subset_1(k2_struct_0(sK6),k2_struct_0(sK8),X0) = k9_subset_1(k2_struct_0(sK6),X0,k2_struct_0(sK8)) ),
    inference(superposition,[status(thm)],[c_5850,c_8650])).

cnf(c_5548,plain,
    ( k9_subset_1(k2_struct_0(X0),X1,k2_struct_0(X2)) = k1_setfam_1(k2_tarski(X1,k2_struct_0(X2)))
    | sP0(X2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4754,c_4738])).

cnf(c_9217,plain,
    ( k9_subset_1(k2_struct_0(sK6),X0,k2_struct_0(sK8)) = k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))) ),
    inference(superposition,[status(thm)],[c_5850,c_5548])).

cnf(c_9304,plain,
    ( k9_subset_1(k2_struct_0(sK6),k2_struct_0(sK8),X0) = k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))) ),
    inference(light_normalisation,[status(thm)],[c_9299,c_9217])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4742,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_22,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4753,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5709,plain,
    ( m1_pre_topc(k1_pre_topc(sK6,sK9),sK6) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4742,c_4753])).

cnf(c_6147,plain,
    ( m1_pre_topc(k1_pre_topc(sK6,sK9),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5709,c_35])).

cnf(c_6152,plain,
    ( sP0(k1_pre_topc(sK6,sK9),sK6) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6147,c_4737])).

cnf(c_6804,plain,
    ( sP0(k1_pre_topc(sK6,sK9),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6152,c_35])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_219,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_22])).

cnf(c_220,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_pre_topc(X1,X0))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_219])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_225,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_220,c_23])).

cnf(c_226,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_225])).

cnf(c_4740,plain,
    ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_6439,plain,
    ( k2_struct_0(k1_pre_topc(sK6,sK9)) = sK9
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4742,c_4740])).

cnf(c_4935,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | k2_struct_0(k1_pre_topc(X0,sK9)) = sK9 ),
    inference(instantiation,[status(thm)],[c_226])).

cnf(c_4937,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6)
    | k2_struct_0(k1_pre_topc(sK6,sK9)) = sK9 ),
    inference(instantiation,[status(thm)],[c_4935])).

cnf(c_6605,plain,
    ( k2_struct_0(k1_pre_topc(sK6,sK9)) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6439,c_34,c_33,c_4937])).

cnf(c_6607,plain,
    ( sP0(k1_pre_topc(sK6,sK9),X0) != iProver_top
    | r1_tarski(sK9,k2_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6605,c_4754])).

cnf(c_7240,plain,
    ( r1_tarski(sK9,k2_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6804,c_6607])).

cnf(c_8980,plain,
    ( k9_subset_1(k2_struct_0(sK6),X0,sK9) = k1_setfam_1(k2_tarski(X0,sK9)) ),
    inference(superposition,[status(thm)],[c_7240,c_4738])).

cnf(c_10274,plain,
    ( k1_setfam_1(k2_tarski(k2_struct_0(sK8),sK9)) = k1_setfam_1(k2_tarski(sK9,k2_struct_0(sK8))) ),
    inference(superposition,[status(thm)],[c_9304,c_8980])).

cnf(c_5708,plain,
    ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4745,c_4753])).

cnf(c_978,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK6 != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_979,plain,
    ( ~ l1_pre_topc(sK6)
    | l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_978])).

cnf(c_980,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_979])).

cnf(c_5950,plain,
    ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5708,c_35,c_980])).

cnf(c_5955,plain,
    ( sP0(k1_pre_topc(sK8,sK9),sK8) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5950,c_4737])).

cnf(c_6798,plain,
    ( sP0(k1_pre_topc(sK8,sK9),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5955,c_35,c_980])).

cnf(c_6438,plain,
    ( k2_struct_0(k1_pre_topc(sK8,sK9)) = sK9
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4745,c_4740])).

cnf(c_6594,plain,
    ( k2_struct_0(k1_pre_topc(sK8,sK9)) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6438,c_35,c_980])).

cnf(c_6596,plain,
    ( sP0(k1_pre_topc(sK8,sK9),X0) != iProver_top
    | r1_tarski(sK9,k2_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6594,c_4754])).

cnf(c_6861,plain,
    ( r1_tarski(sK9,k2_struct_0(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6798,c_6596])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_4768,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8114,plain,
    ( k1_setfam_1(k2_tarski(sK9,k2_struct_0(sK8))) = sK9 ),
    inference(superposition,[status(thm)],[c_6861,c_4768])).

cnf(c_10276,plain,
    ( k1_setfam_1(k2_tarski(k2_struct_0(sK8),sK9)) = sK9 ),
    inference(light_normalisation,[status(thm)],[c_10274,c_8114])).

cnf(c_28246,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)),sK8) = iProver_top
    | v4_pre_topc(sK9,X0) != iProver_top
    | m1_pre_topc(sK8,X0) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(sK9,u1_struct_0(sK8)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28231,c_10276])).

cnf(c_28247,plain,
    ( v4_pre_topc(k1_setfam_1(k2_tarski(k2_struct_0(sK8),sK9)),sK8) = iProver_top
    | v4_pre_topc(sK9,X0) != iProver_top
    | m1_pre_topc(sK8,X0) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(sK9,u1_struct_0(sK8)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_28246,c_8658])).

cnf(c_28248,plain,
    ( v4_pre_topc(sK9,X0) != iProver_top
    | v4_pre_topc(sK9,sK8) = iProver_top
    | m1_pre_topc(sK8,X0) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(sK9,u1_struct_0(sK8)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28247,c_10276])).

cnf(c_28259,plain,
    ( v4_pre_topc(sK9,sK6) != iProver_top
    | v4_pre_topc(sK9,sK8) = iProver_top
    | m1_pre_topc(sK8,sK6) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_tarski(sK9,u1_struct_0(sK8)) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_28248])).

cnf(c_29,negated_conjecture,
    ( ~ v4_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_40,plain,
    ( v4_pre_topc(sK9,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_31,negated_conjecture,
    ( v4_pre_topc(sK9,sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_38,plain,
    ( v4_pre_topc(sK9,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_37,plain,
    ( m1_pre_topc(sK8,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_36,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28259,c_5128,c_40,c_38,c_37,c_36,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:04:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.95/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.95/1.47  
% 7.95/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.95/1.47  
% 7.95/1.47  ------  iProver source info
% 7.95/1.47  
% 7.95/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.95/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.95/1.47  git: non_committed_changes: false
% 7.95/1.47  git: last_make_outside_of_git: false
% 7.95/1.47  
% 7.95/1.47  ------ 
% 7.95/1.47  
% 7.95/1.47  ------ Input Options
% 7.95/1.47  
% 7.95/1.47  --out_options                           all
% 7.95/1.47  --tptp_safe_out                         true
% 7.95/1.47  --problem_path                          ""
% 7.95/1.47  --include_path                          ""
% 7.95/1.47  --clausifier                            res/vclausify_rel
% 7.95/1.47  --clausifier_options                    ""
% 7.95/1.47  --stdin                                 false
% 7.95/1.47  --stats_out                             all
% 7.95/1.47  
% 7.95/1.47  ------ General Options
% 7.95/1.47  
% 7.95/1.47  --fof                                   false
% 7.95/1.47  --time_out_real                         305.
% 7.95/1.47  --time_out_virtual                      -1.
% 7.95/1.47  --symbol_type_check                     false
% 7.95/1.47  --clausify_out                          false
% 7.95/1.47  --sig_cnt_out                           false
% 7.95/1.47  --trig_cnt_out                          false
% 7.95/1.47  --trig_cnt_out_tolerance                1.
% 7.95/1.47  --trig_cnt_out_sk_spl                   false
% 7.95/1.47  --abstr_cl_out                          false
% 7.95/1.47  
% 7.95/1.47  ------ Global Options
% 7.95/1.47  
% 7.95/1.47  --schedule                              default
% 7.95/1.47  --add_important_lit                     false
% 7.95/1.47  --prop_solver_per_cl                    1000
% 7.95/1.47  --min_unsat_core                        false
% 7.95/1.47  --soft_assumptions                      false
% 7.95/1.47  --soft_lemma_size                       3
% 7.95/1.47  --prop_impl_unit_size                   0
% 7.95/1.47  --prop_impl_unit                        []
% 7.95/1.47  --share_sel_clauses                     true
% 7.95/1.47  --reset_solvers                         false
% 7.95/1.47  --bc_imp_inh                            [conj_cone]
% 7.95/1.47  --conj_cone_tolerance                   3.
% 7.95/1.47  --extra_neg_conj                        none
% 7.95/1.47  --large_theory_mode                     true
% 7.95/1.47  --prolific_symb_bound                   200
% 7.95/1.47  --lt_threshold                          2000
% 7.95/1.47  --clause_weak_htbl                      true
% 7.95/1.47  --gc_record_bc_elim                     false
% 7.95/1.47  
% 7.95/1.47  ------ Preprocessing Options
% 7.95/1.47  
% 7.95/1.47  --preprocessing_flag                    true
% 7.95/1.47  --time_out_prep_mult                    0.1
% 7.95/1.47  --splitting_mode                        input
% 7.95/1.47  --splitting_grd                         true
% 7.95/1.47  --splitting_cvd                         false
% 7.95/1.47  --splitting_cvd_svl                     false
% 7.95/1.47  --splitting_nvd                         32
% 7.95/1.47  --sub_typing                            true
% 7.95/1.47  --prep_gs_sim                           true
% 7.95/1.47  --prep_unflatten                        true
% 7.95/1.47  --prep_res_sim                          true
% 7.95/1.47  --prep_upred                            true
% 7.95/1.47  --prep_sem_filter                       exhaustive
% 7.95/1.47  --prep_sem_filter_out                   false
% 7.95/1.47  --pred_elim                             true
% 7.95/1.47  --res_sim_input                         true
% 7.95/1.47  --eq_ax_congr_red                       true
% 7.95/1.47  --pure_diseq_elim                       true
% 7.95/1.47  --brand_transform                       false
% 7.95/1.47  --non_eq_to_eq                          false
% 7.95/1.47  --prep_def_merge                        true
% 7.95/1.47  --prep_def_merge_prop_impl              false
% 7.95/1.47  --prep_def_merge_mbd                    true
% 7.95/1.47  --prep_def_merge_tr_red                 false
% 7.95/1.47  --prep_def_merge_tr_cl                  false
% 7.95/1.47  --smt_preprocessing                     true
% 7.95/1.47  --smt_ac_axioms                         fast
% 7.95/1.47  --preprocessed_out                      false
% 7.95/1.47  --preprocessed_stats                    false
% 7.95/1.47  
% 7.95/1.47  ------ Abstraction refinement Options
% 7.95/1.47  
% 7.95/1.47  --abstr_ref                             []
% 7.95/1.47  --abstr_ref_prep                        false
% 7.95/1.47  --abstr_ref_until_sat                   false
% 7.95/1.47  --abstr_ref_sig_restrict                funpre
% 7.95/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.95/1.47  --abstr_ref_under                       []
% 7.95/1.47  
% 7.95/1.47  ------ SAT Options
% 7.95/1.47  
% 7.95/1.47  --sat_mode                              false
% 7.95/1.47  --sat_fm_restart_options                ""
% 7.95/1.47  --sat_gr_def                            false
% 7.95/1.47  --sat_epr_types                         true
% 7.95/1.47  --sat_non_cyclic_types                  false
% 7.95/1.47  --sat_finite_models                     false
% 7.95/1.47  --sat_fm_lemmas                         false
% 7.95/1.47  --sat_fm_prep                           false
% 7.95/1.47  --sat_fm_uc_incr                        true
% 7.95/1.47  --sat_out_model                         small
% 7.95/1.47  --sat_out_clauses                       false
% 7.95/1.47  
% 7.95/1.47  ------ QBF Options
% 7.95/1.47  
% 7.95/1.47  --qbf_mode                              false
% 7.95/1.47  --qbf_elim_univ                         false
% 7.95/1.47  --qbf_dom_inst                          none
% 7.95/1.47  --qbf_dom_pre_inst                      false
% 7.95/1.47  --qbf_sk_in                             false
% 7.95/1.47  --qbf_pred_elim                         true
% 7.95/1.47  --qbf_split                             512
% 7.95/1.47  
% 7.95/1.47  ------ BMC1 Options
% 7.95/1.47  
% 7.95/1.47  --bmc1_incremental                      false
% 7.95/1.47  --bmc1_axioms                           reachable_all
% 7.95/1.47  --bmc1_min_bound                        0
% 7.95/1.47  --bmc1_max_bound                        -1
% 7.95/1.47  --bmc1_max_bound_default                -1
% 7.95/1.47  --bmc1_symbol_reachability              true
% 7.95/1.47  --bmc1_property_lemmas                  false
% 7.95/1.47  --bmc1_k_induction                      false
% 7.95/1.47  --bmc1_non_equiv_states                 false
% 7.95/1.47  --bmc1_deadlock                         false
% 7.95/1.47  --bmc1_ucm                              false
% 7.95/1.47  --bmc1_add_unsat_core                   none
% 7.95/1.47  --bmc1_unsat_core_children              false
% 7.95/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.95/1.47  --bmc1_out_stat                         full
% 7.95/1.47  --bmc1_ground_init                      false
% 7.95/1.47  --bmc1_pre_inst_next_state              false
% 7.95/1.47  --bmc1_pre_inst_state                   false
% 7.95/1.47  --bmc1_pre_inst_reach_state             false
% 7.95/1.47  --bmc1_out_unsat_core                   false
% 7.95/1.47  --bmc1_aig_witness_out                  false
% 7.95/1.47  --bmc1_verbose                          false
% 7.95/1.47  --bmc1_dump_clauses_tptp                false
% 7.95/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.95/1.47  --bmc1_dump_file                        -
% 7.95/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.95/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.95/1.47  --bmc1_ucm_extend_mode                  1
% 7.95/1.47  --bmc1_ucm_init_mode                    2
% 7.95/1.47  --bmc1_ucm_cone_mode                    none
% 7.95/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.95/1.47  --bmc1_ucm_relax_model                  4
% 7.95/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.95/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.95/1.47  --bmc1_ucm_layered_model                none
% 7.95/1.47  --bmc1_ucm_max_lemma_size               10
% 7.95/1.47  
% 7.95/1.47  ------ AIG Options
% 7.95/1.47  
% 7.95/1.47  --aig_mode                              false
% 7.95/1.47  
% 7.95/1.47  ------ Instantiation Options
% 7.95/1.47  
% 7.95/1.47  --instantiation_flag                    true
% 7.95/1.47  --inst_sos_flag                         true
% 7.95/1.47  --inst_sos_phase                        true
% 7.95/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.95/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.95/1.47  --inst_lit_sel_side                     num_symb
% 7.95/1.47  --inst_solver_per_active                1400
% 7.95/1.47  --inst_solver_calls_frac                1.
% 7.95/1.47  --inst_passive_queue_type               priority_queues
% 7.95/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.95/1.47  --inst_passive_queues_freq              [25;2]
% 7.95/1.47  --inst_dismatching                      true
% 7.95/1.47  --inst_eager_unprocessed_to_passive     true
% 7.95/1.47  --inst_prop_sim_given                   true
% 7.95/1.47  --inst_prop_sim_new                     false
% 7.95/1.47  --inst_subs_new                         false
% 7.95/1.47  --inst_eq_res_simp                      false
% 7.95/1.47  --inst_subs_given                       false
% 7.95/1.47  --inst_orphan_elimination               true
% 7.95/1.47  --inst_learning_loop_flag               true
% 7.95/1.47  --inst_learning_start                   3000
% 7.95/1.47  --inst_learning_factor                  2
% 7.95/1.47  --inst_start_prop_sim_after_learn       3
% 7.95/1.47  --inst_sel_renew                        solver
% 7.95/1.47  --inst_lit_activity_flag                true
% 7.95/1.47  --inst_restr_to_given                   false
% 7.95/1.47  --inst_activity_threshold               500
% 7.95/1.47  --inst_out_proof                        true
% 7.95/1.47  
% 7.95/1.47  ------ Resolution Options
% 7.95/1.47  
% 7.95/1.47  --resolution_flag                       true
% 7.95/1.47  --res_lit_sel                           adaptive
% 7.95/1.47  --res_lit_sel_side                      none
% 7.95/1.47  --res_ordering                          kbo
% 7.95/1.47  --res_to_prop_solver                    active
% 7.95/1.47  --res_prop_simpl_new                    false
% 7.95/1.47  --res_prop_simpl_given                  true
% 7.95/1.47  --res_passive_queue_type                priority_queues
% 7.95/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.95/1.47  --res_passive_queues_freq               [15;5]
% 7.95/1.47  --res_forward_subs                      full
% 7.95/1.47  --res_backward_subs                     full
% 7.95/1.47  --res_forward_subs_resolution           true
% 7.95/1.47  --res_backward_subs_resolution          true
% 7.95/1.47  --res_orphan_elimination                true
% 7.95/1.47  --res_time_limit                        2.
% 7.95/1.47  --res_out_proof                         true
% 7.95/1.47  
% 7.95/1.47  ------ Superposition Options
% 7.95/1.47  
% 7.95/1.47  --superposition_flag                    true
% 7.95/1.47  --sup_passive_queue_type                priority_queues
% 7.95/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.95/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.95/1.47  --demod_completeness_check              fast
% 7.95/1.47  --demod_use_ground                      true
% 7.95/1.47  --sup_to_prop_solver                    passive
% 7.95/1.47  --sup_prop_simpl_new                    true
% 7.95/1.47  --sup_prop_simpl_given                  true
% 7.95/1.47  --sup_fun_splitting                     true
% 7.95/1.47  --sup_smt_interval                      50000
% 7.95/1.47  
% 7.95/1.47  ------ Superposition Simplification Setup
% 7.95/1.47  
% 7.95/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.95/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.95/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.95/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.95/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.95/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.95/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.95/1.47  --sup_immed_triv                        [TrivRules]
% 7.95/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.95/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.95/1.47  --sup_immed_bw_main                     []
% 7.95/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.95/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.95/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.95/1.47  --sup_input_bw                          []
% 7.95/1.47  
% 7.95/1.47  ------ Combination Options
% 7.95/1.47  
% 7.95/1.47  --comb_res_mult                         3
% 7.95/1.47  --comb_sup_mult                         2
% 7.95/1.47  --comb_inst_mult                        10
% 7.95/1.47  
% 7.95/1.47  ------ Debug Options
% 7.95/1.47  
% 7.95/1.47  --dbg_backtrace                         false
% 7.95/1.47  --dbg_dump_prop_clauses                 false
% 7.95/1.47  --dbg_dump_prop_clauses_file            -
% 7.95/1.47  --dbg_out_stat                          false
% 7.95/1.47  ------ Parsing...
% 7.95/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.95/1.47  
% 7.95/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.95/1.47  
% 7.95/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.95/1.47  
% 7.95/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.95/1.47  ------ Proving...
% 7.95/1.47  ------ Problem Properties 
% 7.95/1.47  
% 7.95/1.47  
% 7.95/1.47  clauses                                 34
% 7.95/1.47  conjectures                             6
% 7.95/1.47  EPR                                     7
% 7.95/1.47  Horn                                    30
% 7.95/1.47  unary                                   8
% 7.95/1.47  binary                                  6
% 7.95/1.47  lits                                    103
% 7.95/1.47  lits eq                                 10
% 7.95/1.47  fd_pure                                 0
% 7.95/1.47  fd_pseudo                               0
% 7.95/1.47  fd_cond                                 0
% 7.95/1.47  fd_pseudo_cond                          0
% 7.95/1.47  AC symbols                              0
% 7.95/1.47  
% 7.95/1.47  ------ Schedule dynamic 5 is on 
% 7.95/1.47  
% 7.95/1.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.95/1.47  
% 7.95/1.47  
% 7.95/1.47  ------ 
% 7.95/1.47  Current options:
% 7.95/1.47  ------ 
% 7.95/1.47  
% 7.95/1.47  ------ Input Options
% 7.95/1.47  
% 7.95/1.47  --out_options                           all
% 7.95/1.47  --tptp_safe_out                         true
% 7.95/1.47  --problem_path                          ""
% 7.95/1.47  --include_path                          ""
% 7.95/1.47  --clausifier                            res/vclausify_rel
% 7.95/1.47  --clausifier_options                    ""
% 7.95/1.47  --stdin                                 false
% 7.95/1.47  --stats_out                             all
% 7.95/1.47  
% 7.95/1.47  ------ General Options
% 7.95/1.47  
% 7.95/1.47  --fof                                   false
% 7.95/1.47  --time_out_real                         305.
% 7.95/1.47  --time_out_virtual                      -1.
% 7.95/1.47  --symbol_type_check                     false
% 7.95/1.47  --clausify_out                          false
% 7.95/1.47  --sig_cnt_out                           false
% 7.95/1.47  --trig_cnt_out                          false
% 7.95/1.47  --trig_cnt_out_tolerance                1.
% 7.95/1.47  --trig_cnt_out_sk_spl                   false
% 7.95/1.47  --abstr_cl_out                          false
% 7.95/1.47  
% 7.95/1.47  ------ Global Options
% 7.95/1.47  
% 7.95/1.47  --schedule                              default
% 7.95/1.47  --add_important_lit                     false
% 7.95/1.47  --prop_solver_per_cl                    1000
% 7.95/1.47  --min_unsat_core                        false
% 7.95/1.47  --soft_assumptions                      false
% 7.95/1.47  --soft_lemma_size                       3
% 7.95/1.47  --prop_impl_unit_size                   0
% 7.95/1.47  --prop_impl_unit                        []
% 7.95/1.47  --share_sel_clauses                     true
% 7.95/1.47  --reset_solvers                         false
% 7.95/1.47  --bc_imp_inh                            [conj_cone]
% 7.95/1.47  --conj_cone_tolerance                   3.
% 7.95/1.47  --extra_neg_conj                        none
% 7.95/1.47  --large_theory_mode                     true
% 7.95/1.47  --prolific_symb_bound                   200
% 7.95/1.47  --lt_threshold                          2000
% 7.95/1.47  --clause_weak_htbl                      true
% 7.95/1.47  --gc_record_bc_elim                     false
% 7.95/1.47  
% 7.95/1.47  ------ Preprocessing Options
% 7.95/1.47  
% 7.95/1.47  --preprocessing_flag                    true
% 7.95/1.47  --time_out_prep_mult                    0.1
% 7.95/1.47  --splitting_mode                        input
% 7.95/1.47  --splitting_grd                         true
% 7.95/1.47  --splitting_cvd                         false
% 7.95/1.47  --splitting_cvd_svl                     false
% 7.95/1.47  --splitting_nvd                         32
% 7.95/1.47  --sub_typing                            true
% 7.95/1.47  --prep_gs_sim                           true
% 7.95/1.47  --prep_unflatten                        true
% 7.95/1.47  --prep_res_sim                          true
% 7.95/1.47  --prep_upred                            true
% 7.95/1.47  --prep_sem_filter                       exhaustive
% 7.95/1.47  --prep_sem_filter_out                   false
% 7.95/1.47  --pred_elim                             true
% 7.95/1.47  --res_sim_input                         true
% 7.95/1.47  --eq_ax_congr_red                       true
% 7.95/1.47  --pure_diseq_elim                       true
% 7.95/1.47  --brand_transform                       false
% 7.95/1.47  --non_eq_to_eq                          false
% 7.95/1.47  --prep_def_merge                        true
% 7.95/1.47  --prep_def_merge_prop_impl              false
% 7.95/1.47  --prep_def_merge_mbd                    true
% 7.95/1.47  --prep_def_merge_tr_red                 false
% 7.95/1.47  --prep_def_merge_tr_cl                  false
% 7.95/1.47  --smt_preprocessing                     true
% 7.95/1.47  --smt_ac_axioms                         fast
% 7.95/1.47  --preprocessed_out                      false
% 7.95/1.47  --preprocessed_stats                    false
% 7.95/1.47  
% 7.95/1.47  ------ Abstraction refinement Options
% 7.95/1.47  
% 7.95/1.47  --abstr_ref                             []
% 7.95/1.47  --abstr_ref_prep                        false
% 7.95/1.47  --abstr_ref_until_sat                   false
% 7.95/1.47  --abstr_ref_sig_restrict                funpre
% 7.95/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.95/1.47  --abstr_ref_under                       []
% 7.95/1.47  
% 7.95/1.47  ------ SAT Options
% 7.95/1.47  
% 7.95/1.47  --sat_mode                              false
% 7.95/1.47  --sat_fm_restart_options                ""
% 7.95/1.47  --sat_gr_def                            false
% 7.95/1.47  --sat_epr_types                         true
% 7.95/1.47  --sat_non_cyclic_types                  false
% 7.95/1.47  --sat_finite_models                     false
% 7.95/1.47  --sat_fm_lemmas                         false
% 7.95/1.47  --sat_fm_prep                           false
% 7.95/1.47  --sat_fm_uc_incr                        true
% 7.95/1.47  --sat_out_model                         small
% 7.95/1.47  --sat_out_clauses                       false
% 7.95/1.47  
% 7.95/1.47  ------ QBF Options
% 7.95/1.47  
% 7.95/1.47  --qbf_mode                              false
% 7.95/1.47  --qbf_elim_univ                         false
% 7.95/1.47  --qbf_dom_inst                          none
% 7.95/1.47  --qbf_dom_pre_inst                      false
% 7.95/1.47  --qbf_sk_in                             false
% 7.95/1.47  --qbf_pred_elim                         true
% 7.95/1.47  --qbf_split                             512
% 7.95/1.47  
% 7.95/1.47  ------ BMC1 Options
% 7.95/1.47  
% 7.95/1.47  --bmc1_incremental                      false
% 7.95/1.47  --bmc1_axioms                           reachable_all
% 7.95/1.47  --bmc1_min_bound                        0
% 7.95/1.47  --bmc1_max_bound                        -1
% 7.95/1.47  --bmc1_max_bound_default                -1
% 7.95/1.47  --bmc1_symbol_reachability              true
% 7.95/1.47  --bmc1_property_lemmas                  false
% 7.95/1.47  --bmc1_k_induction                      false
% 7.95/1.47  --bmc1_non_equiv_states                 false
% 7.95/1.47  --bmc1_deadlock                         false
% 7.95/1.47  --bmc1_ucm                              false
% 7.95/1.47  --bmc1_add_unsat_core                   none
% 7.95/1.47  --bmc1_unsat_core_children              false
% 7.95/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.95/1.47  --bmc1_out_stat                         full
% 7.95/1.47  --bmc1_ground_init                      false
% 7.95/1.47  --bmc1_pre_inst_next_state              false
% 7.95/1.47  --bmc1_pre_inst_state                   false
% 7.95/1.47  --bmc1_pre_inst_reach_state             false
% 7.95/1.47  --bmc1_out_unsat_core                   false
% 7.95/1.47  --bmc1_aig_witness_out                  false
% 7.95/1.47  --bmc1_verbose                          false
% 7.95/1.47  --bmc1_dump_clauses_tptp                false
% 7.95/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.95/1.47  --bmc1_dump_file                        -
% 7.95/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.95/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.95/1.47  --bmc1_ucm_extend_mode                  1
% 7.95/1.47  --bmc1_ucm_init_mode                    2
% 7.95/1.47  --bmc1_ucm_cone_mode                    none
% 7.95/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.95/1.47  --bmc1_ucm_relax_model                  4
% 7.95/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.95/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.95/1.47  --bmc1_ucm_layered_model                none
% 7.95/1.47  --bmc1_ucm_max_lemma_size               10
% 7.95/1.47  
% 7.95/1.47  ------ AIG Options
% 7.95/1.47  
% 7.95/1.47  --aig_mode                              false
% 7.95/1.47  
% 7.95/1.47  ------ Instantiation Options
% 7.95/1.47  
% 7.95/1.47  --instantiation_flag                    true
% 7.95/1.47  --inst_sos_flag                         true
% 7.95/1.47  --inst_sos_phase                        true
% 7.95/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.95/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.95/1.47  --inst_lit_sel_side                     none
% 7.95/1.47  --inst_solver_per_active                1400
% 7.95/1.47  --inst_solver_calls_frac                1.
% 7.95/1.47  --inst_passive_queue_type               priority_queues
% 7.95/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.95/1.47  --inst_passive_queues_freq              [25;2]
% 7.95/1.47  --inst_dismatching                      true
% 7.95/1.47  --inst_eager_unprocessed_to_passive     true
% 7.95/1.47  --inst_prop_sim_given                   true
% 7.95/1.47  --inst_prop_sim_new                     false
% 7.95/1.47  --inst_subs_new                         false
% 7.95/1.47  --inst_eq_res_simp                      false
% 7.95/1.47  --inst_subs_given                       false
% 7.95/1.47  --inst_orphan_elimination               true
% 7.95/1.47  --inst_learning_loop_flag               true
% 7.95/1.47  --inst_learning_start                   3000
% 7.95/1.47  --inst_learning_factor                  2
% 7.95/1.47  --inst_start_prop_sim_after_learn       3
% 7.95/1.47  --inst_sel_renew                        solver
% 7.95/1.47  --inst_lit_activity_flag                true
% 7.95/1.47  --inst_restr_to_given                   false
% 7.95/1.47  --inst_activity_threshold               500
% 7.95/1.47  --inst_out_proof                        true
% 7.95/1.47  
% 7.95/1.47  ------ Resolution Options
% 7.95/1.47  
% 7.95/1.47  --resolution_flag                       false
% 7.95/1.47  --res_lit_sel                           adaptive
% 7.95/1.47  --res_lit_sel_side                      none
% 7.95/1.47  --res_ordering                          kbo
% 7.95/1.47  --res_to_prop_solver                    active
% 7.95/1.47  --res_prop_simpl_new                    false
% 7.95/1.47  --res_prop_simpl_given                  true
% 7.95/1.47  --res_passive_queue_type                priority_queues
% 7.95/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.95/1.47  --res_passive_queues_freq               [15;5]
% 7.95/1.47  --res_forward_subs                      full
% 7.95/1.47  --res_backward_subs                     full
% 7.95/1.47  --res_forward_subs_resolution           true
% 7.95/1.47  --res_backward_subs_resolution          true
% 7.95/1.47  --res_orphan_elimination                true
% 7.95/1.47  --res_time_limit                        2.
% 7.95/1.47  --res_out_proof                         true
% 7.95/1.47  
% 7.95/1.47  ------ Superposition Options
% 7.95/1.47  
% 7.95/1.47  --superposition_flag                    true
% 7.95/1.47  --sup_passive_queue_type                priority_queues
% 7.95/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.95/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.95/1.47  --demod_completeness_check              fast
% 7.95/1.47  --demod_use_ground                      true
% 7.95/1.47  --sup_to_prop_solver                    passive
% 7.95/1.47  --sup_prop_simpl_new                    true
% 7.95/1.47  --sup_prop_simpl_given                  true
% 7.95/1.47  --sup_fun_splitting                     true
% 7.95/1.47  --sup_smt_interval                      50000
% 7.95/1.47  
% 7.95/1.47  ------ Superposition Simplification Setup
% 7.95/1.47  
% 7.95/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.95/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.95/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.95/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.95/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.95/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.95/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.95/1.47  --sup_immed_triv                        [TrivRules]
% 7.95/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.95/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.95/1.47  --sup_immed_bw_main                     []
% 7.95/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.95/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.95/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.95/1.47  --sup_input_bw                          []
% 7.95/1.47  
% 7.95/1.47  ------ Combination Options
% 7.95/1.47  
% 7.95/1.47  --comb_res_mult                         3
% 7.95/1.47  --comb_sup_mult                         2
% 7.95/1.47  --comb_inst_mult                        10
% 7.95/1.47  
% 7.95/1.47  ------ Debug Options
% 7.95/1.47  
% 7.95/1.47  --dbg_backtrace                         false
% 7.95/1.47  --dbg_dump_prop_clauses                 false
% 7.95/1.47  --dbg_dump_prop_clauses_file            -
% 7.95/1.47  --dbg_out_stat                          false
% 7.95/1.47  
% 7.95/1.47  
% 7.95/1.47  
% 7.95/1.47  
% 7.95/1.47  ------ Proving...
% 7.95/1.47  
% 7.95/1.47  
% 7.95/1.47  % SZS status Theorem for theBenchmark.p
% 7.95/1.47  
% 7.95/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.95/1.47  
% 7.95/1.47  fof(f13,conjecture,(
% 7.95/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 7.95/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.47  
% 7.95/1.47  fof(f14,negated_conjecture,(
% 7.95/1.47    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 7.95/1.47    inference(negated_conjecture,[],[f13])).
% 7.95/1.47  
% 7.95/1.47  fof(f25,plain,(
% 7.95/1.47    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v4_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.95/1.47    inference(ennf_transformation,[],[f14])).
% 7.95/1.47  
% 7.95/1.47  fof(f26,plain,(
% 7.95/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.95/1.47    inference(flattening,[],[f25])).
% 7.95/1.47  
% 7.95/1.47  fof(f47,plain,(
% 7.95/1.47    ( ! [X2,X1] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) => (~v4_pre_topc(sK9,X2) & sK9 = X1 & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X2))))) )),
% 7.95/1.47    introduced(choice_axiom,[])).
% 7.95/1.47  
% 7.95/1.47  fof(f46,plain,(
% 7.95/1.47    ( ! [X0,X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) => (? [X3] : (~v4_pre_topc(X3,sK8) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8)))) & v4_pre_topc(X1,X0) & m1_pre_topc(sK8,X0))) )),
% 7.95/1.47    introduced(choice_axiom,[])).
% 7.95/1.47  
% 7.95/1.47  fof(f45,plain,(
% 7.95/1.47    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & sK7 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(sK7,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.95/1.47    introduced(choice_axiom,[])).
% 7.95/1.47  
% 7.95/1.47  fof(f44,plain,(
% 7.95/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,sK6) & m1_pre_topc(X2,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6))),
% 7.95/1.47    introduced(choice_axiom,[])).
% 7.95/1.47  
% 7.95/1.47  fof(f48,plain,(
% 7.95/1.47    (((~v4_pre_topc(sK9,sK8) & sK7 = sK9 & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))) & v4_pre_topc(sK7,sK6) & m1_pre_topc(sK8,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6)),
% 7.95/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f26,f47,f46,f45,f44])).
% 7.95/1.47  
% 7.95/1.47  fof(f83,plain,(
% 7.95/1.47    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))),
% 7.95/1.47    inference(cnf_transformation,[],[f48])).
% 7.95/1.47  
% 7.95/1.47  fof(f7,axiom,(
% 7.95/1.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.95/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.47  
% 7.95/1.47  fof(f30,plain,(
% 7.95/1.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.95/1.47    inference(nnf_transformation,[],[f7])).
% 7.95/1.47  
% 7.95/1.47  fof(f55,plain,(
% 7.95/1.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.95/1.47    inference(cnf_transformation,[],[f30])).
% 7.95/1.47  
% 7.95/1.47  fof(f2,axiom,(
% 7.95/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 7.95/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.47  
% 7.95/1.47  fof(f16,plain,(
% 7.95/1.47    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.95/1.47    inference(ennf_transformation,[],[f2])).
% 7.95/1.47  
% 7.95/1.47  fof(f50,plain,(
% 7.95/1.47    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.95/1.47    inference(cnf_transformation,[],[f16])).
% 7.95/1.47  
% 7.95/1.47  fof(f56,plain,(
% 7.95/1.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.95/1.47    inference(cnf_transformation,[],[f30])).
% 7.95/1.47  
% 7.95/1.47  fof(f5,axiom,(
% 7.95/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.95/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.47  
% 7.95/1.47  fof(f17,plain,(
% 7.95/1.47    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.95/1.47    inference(ennf_transformation,[],[f5])).
% 7.95/1.47  
% 7.95/1.47  fof(f53,plain,(
% 7.95/1.47    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.95/1.47    inference(cnf_transformation,[],[f17])).
% 7.95/1.47  
% 7.95/1.47  fof(f6,axiom,(
% 7.95/1.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.95/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.47  
% 7.95/1.47  fof(f54,plain,(
% 7.95/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.95/1.47    inference(cnf_transformation,[],[f6])).
% 7.95/1.47  
% 7.95/1.47  fof(f87,plain,(
% 7.95/1.47    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.95/1.47    inference(definition_unfolding,[],[f53,f54])).
% 7.95/1.47  
% 7.95/1.47  fof(f12,axiom,(
% 7.95/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 7.95/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.47  
% 7.95/1.47  fof(f24,plain,(
% 7.95/1.47    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.95/1.47    inference(ennf_transformation,[],[f12])).
% 7.95/1.47  
% 7.95/1.47  fof(f40,plain,(
% 7.95/1.47    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.95/1.47    inference(nnf_transformation,[],[f24])).
% 7.95/1.47  
% 7.95/1.47  fof(f41,plain,(
% 7.95/1.47    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v4_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.95/1.47    inference(rectify,[],[f40])).
% 7.95/1.47  
% 7.95/1.47  fof(f42,plain,(
% 7.95/1.47    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v4_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2 & v4_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.95/1.47    introduced(choice_axiom,[])).
% 7.95/1.47  
% 7.95/1.47  fof(f43,plain,(
% 7.95/1.47    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2 & v4_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.95/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).
% 7.95/1.47  
% 7.95/1.47  fof(f78,plain,(
% 7.95/1.47    ( ! [X2,X0,X3,X1] : (v4_pre_topc(X2,X1) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.95/1.47    inference(cnf_transformation,[],[f43])).
% 7.95/1.47  
% 7.95/1.47  fof(f93,plain,(
% 7.95/1.47    ( ! [X0,X3,X1] : (v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.95/1.47    inference(equality_resolution,[],[f78])).
% 7.95/1.47  
% 7.95/1.47  fof(f81,plain,(
% 7.95/1.47    m1_pre_topc(sK8,sK6)),
% 7.95/1.47    inference(cnf_transformation,[],[f48])).
% 7.95/1.47  
% 7.95/1.47  fof(f9,axiom,(
% 7.95/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 7.95/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.47  
% 7.95/1.47  fof(f20,plain,(
% 7.95/1.47    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.95/1.47    inference(ennf_transformation,[],[f9])).
% 7.95/1.47  
% 7.95/1.47  fof(f28,plain,(
% 7.95/1.47    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 7.95/1.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 7.95/1.47  
% 7.95/1.47  fof(f27,plain,(
% 7.95/1.47    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 7.95/1.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.95/1.47  
% 7.95/1.47  fof(f29,plain,(
% 7.95/1.47    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.95/1.47    inference(definition_folding,[],[f20,f28,f27])).
% 7.95/1.47  
% 7.95/1.47  fof(f71,plain,(
% 7.95/1.47    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.95/1.47    inference(cnf_transformation,[],[f29])).
% 7.95/1.47  
% 7.95/1.47  fof(f32,plain,(
% 7.95/1.47    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 7.95/1.47    inference(nnf_transformation,[],[f28])).
% 7.95/1.47  
% 7.95/1.47  fof(f59,plain,(
% 7.95/1.47    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 7.95/1.47    inference(cnf_transformation,[],[f32])).
% 7.95/1.47  
% 7.95/1.47  fof(f11,axiom,(
% 7.95/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.95/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.47  
% 7.95/1.47  fof(f23,plain,(
% 7.95/1.47    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.95/1.47    inference(ennf_transformation,[],[f11])).
% 7.95/1.47  
% 7.95/1.47  fof(f74,plain,(
% 7.95/1.47    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.95/1.47    inference(cnf_transformation,[],[f23])).
% 7.95/1.47  
% 7.95/1.47  fof(f79,plain,(
% 7.95/1.47    l1_pre_topc(sK6)),
% 7.95/1.47    inference(cnf_transformation,[],[f48])).
% 7.95/1.47  
% 7.95/1.47  fof(f33,plain,(
% 7.95/1.47    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 7.95/1.47    inference(nnf_transformation,[],[f27])).
% 7.95/1.47  
% 7.95/1.47  fof(f34,plain,(
% 7.95/1.47    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 7.95/1.47    inference(flattening,[],[f33])).
% 7.95/1.47  
% 7.95/1.47  fof(f35,plain,(
% 7.95/1.47    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 7.95/1.47    inference(rectify,[],[f34])).
% 7.95/1.47  
% 7.95/1.47  fof(f38,plain,(
% 7.95/1.47    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 7.95/1.47    introduced(choice_axiom,[])).
% 7.95/1.47  
% 7.95/1.47  fof(f37,plain,(
% 7.95/1.47    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 7.95/1.47    introduced(choice_axiom,[])).
% 7.95/1.47  
% 7.95/1.47  fof(f36,plain,(
% 7.95/1.47    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.95/1.47    introduced(choice_axiom,[])).
% 7.95/1.47  
% 7.95/1.47  fof(f39,plain,(
% 7.95/1.47    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 7.95/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f38,f37,f36])).
% 7.95/1.47  
% 7.95/1.47  fof(f61,plain,(
% 7.95/1.47    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 7.95/1.47    inference(cnf_transformation,[],[f39])).
% 7.95/1.47  
% 7.95/1.47  fof(f80,plain,(
% 7.95/1.47    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 7.95/1.47    inference(cnf_transformation,[],[f48])).
% 7.95/1.47  
% 7.95/1.47  fof(f84,plain,(
% 7.95/1.47    sK7 = sK9),
% 7.95/1.47    inference(cnf_transformation,[],[f48])).
% 7.95/1.47  
% 7.95/1.47  fof(f89,plain,(
% 7.95/1.47    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6)))),
% 7.95/1.47    inference(definition_unfolding,[],[f80,f84])).
% 7.95/1.47  
% 7.95/1.47  fof(f10,axiom,(
% 7.95/1.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 7.95/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.47  
% 7.95/1.47  fof(f21,plain,(
% 7.95/1.47    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.95/1.47    inference(ennf_transformation,[],[f10])).
% 7.95/1.47  
% 7.95/1.47  fof(f22,plain,(
% 7.95/1.47    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.95/1.47    inference(flattening,[],[f21])).
% 7.95/1.47  
% 7.95/1.47  fof(f73,plain,(
% 7.95/1.47    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.95/1.47    inference(cnf_transformation,[],[f22])).
% 7.95/1.47  
% 7.95/1.47  fof(f8,axiom,(
% 7.95/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 7.95/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.47  
% 7.95/1.47  fof(f18,plain,(
% 7.95/1.47    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.95/1.47    inference(ennf_transformation,[],[f8])).
% 7.95/1.47  
% 7.95/1.47  fof(f19,plain,(
% 7.95/1.47    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.95/1.47    inference(flattening,[],[f18])).
% 7.95/1.47  
% 7.95/1.47  fof(f31,plain,(
% 7.95/1.47    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.95/1.47    inference(nnf_transformation,[],[f19])).
% 7.95/1.47  
% 7.95/1.47  fof(f57,plain,(
% 7.95/1.47    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.95/1.47    inference(cnf_transformation,[],[f31])).
% 7.95/1.47  
% 7.95/1.47  fof(f91,plain,(
% 7.95/1.47    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.95/1.47    inference(equality_resolution,[],[f57])).
% 7.95/1.47  
% 7.95/1.47  fof(f72,plain,(
% 7.95/1.47    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.95/1.47    inference(cnf_transformation,[],[f22])).
% 7.95/1.47  
% 7.95/1.47  fof(f1,axiom,(
% 7.95/1.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.95/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.47  
% 7.95/1.47  fof(f15,plain,(
% 7.95/1.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.95/1.47    inference(ennf_transformation,[],[f1])).
% 7.95/1.47  
% 7.95/1.47  fof(f49,plain,(
% 7.95/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.95/1.47    inference(cnf_transformation,[],[f15])).
% 7.95/1.47  
% 7.95/1.47  fof(f86,plain,(
% 7.95/1.47    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.95/1.47    inference(definition_unfolding,[],[f49,f54])).
% 7.95/1.47  
% 7.95/1.47  fof(f85,plain,(
% 7.95/1.47    ~v4_pre_topc(sK9,sK8)),
% 7.95/1.47    inference(cnf_transformation,[],[f48])).
% 7.95/1.47  
% 7.95/1.47  fof(f82,plain,(
% 7.95/1.47    v4_pre_topc(sK7,sK6)),
% 7.95/1.47    inference(cnf_transformation,[],[f48])).
% 7.95/1.47  
% 7.95/1.47  fof(f88,plain,(
% 7.95/1.47    v4_pre_topc(sK9,sK6)),
% 7.95/1.47    inference(definition_unfolding,[],[f82,f84])).
% 7.95/1.47  
% 7.95/1.47  cnf(c_30,negated_conjecture,
% 7.95/1.47      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
% 7.95/1.47      inference(cnf_transformation,[],[f83]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_4745,plain,
% 7.95/1.47      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 7.95/1.47      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_6,plain,
% 7.95/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.95/1.47      inference(cnf_transformation,[],[f55]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_4765,plain,
% 7.95/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.95/1.47      | r1_tarski(X0,X1) = iProver_top ),
% 7.95/1.47      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_5128,plain,
% 7.95/1.47      ( r1_tarski(sK9,u1_struct_0(sK8)) = iProver_top ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_4745,c_4765]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_1,plain,
% 7.95/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.95/1.47      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 7.95/1.47      inference(cnf_transformation,[],[f50]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_5,plain,
% 7.95/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.95/1.47      inference(cnf_transformation,[],[f56]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_280,plain,
% 7.95/1.47      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.95/1.47      inference(prop_impl,[status(thm)],[c_5]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_281,plain,
% 7.95/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.95/1.47      inference(renaming,[status(thm)],[c_280]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_344,plain,
% 7.95/1.47      ( ~ r1_tarski(X0,X1)
% 7.95/1.47      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 7.95/1.47      inference(bin_hyper_res,[status(thm)],[c_1,c_281]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_4739,plain,
% 7.95/1.47      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
% 7.95/1.47      | r1_tarski(X1,X0) != iProver_top ),
% 7.95/1.47      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_8651,plain,
% 7.95/1.47      ( k9_subset_1(u1_struct_0(sK8),sK9,X0) = k9_subset_1(u1_struct_0(sK8),X0,sK9) ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_5128,c_4739]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_4,plain,
% 7.95/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.95/1.47      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 7.95/1.47      inference(cnf_transformation,[],[f87]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_345,plain,
% 7.95/1.47      ( ~ r1_tarski(X0,X1)
% 7.95/1.47      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 7.95/1.47      inference(bin_hyper_res,[status(thm)],[c_4,c_281]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_4738,plain,
% 7.95/1.47      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 7.95/1.47      | r1_tarski(X2,X0) != iProver_top ),
% 7.95/1.47      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_5549,plain,
% 7.95/1.47      ( k9_subset_1(u1_struct_0(sK8),X0,sK9) = k1_setfam_1(k2_tarski(X0,sK9)) ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_5128,c_4738]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_8658,plain,
% 7.95/1.47      ( k9_subset_1(u1_struct_0(sK8),sK9,X0) = k1_setfam_1(k2_tarski(X0,sK9)) ),
% 7.95/1.47      inference(light_normalisation,[status(thm)],[c_8651,c_5549]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_4766,plain,
% 7.95/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.95/1.47      | r1_tarski(X0,X1) != iProver_top ),
% 7.95/1.47      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_25,plain,
% 7.95/1.47      ( ~ v4_pre_topc(X0,X1)
% 7.95/1.47      | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
% 7.95/1.47      | ~ m1_pre_topc(X2,X1)
% 7.95/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.95/1.47      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
% 7.95/1.47      | ~ l1_pre_topc(X1) ),
% 7.95/1.47      inference(cnf_transformation,[],[f93]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_4750,plain,
% 7.95/1.47      ( v4_pre_topc(X0,X1) != iProver_top
% 7.95/1.47      | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2) = iProver_top
% 7.95/1.47      | m1_pre_topc(X2,X1) != iProver_top
% 7.95/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.95/1.47      | m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 7.95/1.47      | l1_pre_topc(X1) != iProver_top ),
% 7.95/1.47      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_7517,plain,
% 7.95/1.47      ( v4_pre_topc(X0,X1) != iProver_top
% 7.95/1.47      | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2) = iProver_top
% 7.95/1.47      | m1_pre_topc(X2,X1) != iProver_top
% 7.95/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.95/1.47      | r1_tarski(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),u1_struct_0(X2)) != iProver_top
% 7.95/1.47      | l1_pre_topc(X1) != iProver_top ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_4766,c_4750]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_28231,plain,
% 7.95/1.47      ( v4_pre_topc(k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)),sK8) = iProver_top
% 7.95/1.47      | v4_pre_topc(sK9,X0) != iProver_top
% 7.95/1.47      | m1_pre_topc(sK8,X0) != iProver_top
% 7.95/1.47      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.95/1.47      | r1_tarski(k1_setfam_1(k2_tarski(k2_struct_0(sK8),sK9)),u1_struct_0(sK8)) != iProver_top
% 7.95/1.47      | l1_pre_topc(X0) != iProver_top ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_8658,c_7517]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_32,negated_conjecture,
% 7.95/1.47      ( m1_pre_topc(sK8,sK6) ),
% 7.95/1.47      inference(cnf_transformation,[],[f81]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_4743,plain,
% 7.95/1.47      ( m1_pre_topc(sK8,sK6) = iProver_top ),
% 7.95/1.47      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_21,plain,
% 7.95/1.47      ( sP1(X0,X1) | ~ l1_pre_topc(X0) | ~ l1_pre_topc(X1) ),
% 7.95/1.47      inference(cnf_transformation,[],[f71]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_10,plain,
% 7.95/1.47      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 7.95/1.47      inference(cnf_transformation,[],[f59]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_500,plain,
% 7.95/1.47      ( sP0(X0,X1)
% 7.95/1.47      | ~ m1_pre_topc(X0,X1)
% 7.95/1.47      | ~ l1_pre_topc(X0)
% 7.95/1.47      | ~ l1_pre_topc(X1) ),
% 7.95/1.47      inference(resolution,[status(thm)],[c_21,c_10]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_24,plain,
% 7.95/1.47      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.95/1.47      inference(cnf_transformation,[],[f74]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_504,plain,
% 7.95/1.47      ( ~ m1_pre_topc(X0,X1) | sP0(X0,X1) | ~ l1_pre_topc(X1) ),
% 7.95/1.47      inference(global_propositional_subsumption,
% 7.95/1.47                [status(thm)],
% 7.95/1.47                [c_500,c_24]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_505,plain,
% 7.95/1.47      ( sP0(X0,X1) | ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) ),
% 7.95/1.47      inference(renaming,[status(thm)],[c_504]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_4737,plain,
% 7.95/1.47      ( sP0(X0,X1) = iProver_top
% 7.95/1.47      | m1_pre_topc(X0,X1) != iProver_top
% 7.95/1.47      | l1_pre_topc(X1) != iProver_top ),
% 7.95/1.47      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_5616,plain,
% 7.95/1.47      ( sP0(sK8,sK6) = iProver_top | l1_pre_topc(sK6) != iProver_top ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_4743,c_4737]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_34,negated_conjecture,
% 7.95/1.47      ( l1_pre_topc(sK6) ),
% 7.95/1.47      inference(cnf_transformation,[],[f79]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_35,plain,
% 7.95/1.47      ( l1_pre_topc(sK6) = iProver_top ),
% 7.95/1.47      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_967,plain,
% 7.95/1.47      ( sP0(X0,X1) | ~ l1_pre_topc(X1) | sK6 != X1 | sK8 != X0 ),
% 7.95/1.47      inference(resolution_lifted,[status(thm)],[c_505,c_32]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_968,plain,
% 7.95/1.47      ( sP0(sK8,sK6) | ~ l1_pre_topc(sK6) ),
% 7.95/1.47      inference(unflattening,[status(thm)],[c_967]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_969,plain,
% 7.95/1.47      ( sP0(sK8,sK6) = iProver_top | l1_pre_topc(sK6) != iProver_top ),
% 7.95/1.47      inference(predicate_to_equality,[status(thm)],[c_968]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_5850,plain,
% 7.95/1.47      ( sP0(sK8,sK6) = iProver_top ),
% 7.95/1.47      inference(global_propositional_subsumption,
% 7.95/1.47                [status(thm)],
% 7.95/1.47                [c_5616,c_35,c_969]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_20,plain,
% 7.95/1.47      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 7.95/1.47      inference(cnf_transformation,[],[f61]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_4754,plain,
% 7.95/1.47      ( sP0(X0,X1) != iProver_top
% 7.95/1.47      | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) = iProver_top ),
% 7.95/1.47      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_8650,plain,
% 7.95/1.47      ( k9_subset_1(k2_struct_0(X0),k2_struct_0(X1),X2) = k9_subset_1(k2_struct_0(X0),X2,k2_struct_0(X1))
% 7.95/1.47      | sP0(X1,X0) != iProver_top ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_4754,c_4739]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_9299,plain,
% 7.95/1.47      ( k9_subset_1(k2_struct_0(sK6),k2_struct_0(sK8),X0) = k9_subset_1(k2_struct_0(sK6),X0,k2_struct_0(sK8)) ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_5850,c_8650]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_5548,plain,
% 7.95/1.47      ( k9_subset_1(k2_struct_0(X0),X1,k2_struct_0(X2)) = k1_setfam_1(k2_tarski(X1,k2_struct_0(X2)))
% 7.95/1.47      | sP0(X2,X0) != iProver_top ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_4754,c_4738]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_9217,plain,
% 7.95/1.47      ( k9_subset_1(k2_struct_0(sK6),X0,k2_struct_0(sK8)) = k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))) ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_5850,c_5548]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_9304,plain,
% 7.95/1.47      ( k9_subset_1(k2_struct_0(sK6),k2_struct_0(sK8),X0) = k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))) ),
% 7.95/1.47      inference(light_normalisation,[status(thm)],[c_9299,c_9217]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_33,negated_conjecture,
% 7.95/1.47      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 7.95/1.47      inference(cnf_transformation,[],[f89]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_4742,plain,
% 7.95/1.47      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 7.95/1.47      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_22,plain,
% 7.95/1.47      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 7.95/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.95/1.47      | ~ l1_pre_topc(X0) ),
% 7.95/1.47      inference(cnf_transformation,[],[f73]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_4753,plain,
% 7.95/1.47      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 7.95/1.47      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.95/1.47      | l1_pre_topc(X0) != iProver_top ),
% 7.95/1.47      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_5709,plain,
% 7.95/1.47      ( m1_pre_topc(k1_pre_topc(sK6,sK9),sK6) = iProver_top
% 7.95/1.47      | l1_pre_topc(sK6) != iProver_top ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_4742,c_4753]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_6147,plain,
% 7.95/1.47      ( m1_pre_topc(k1_pre_topc(sK6,sK9),sK6) = iProver_top ),
% 7.95/1.47      inference(global_propositional_subsumption,
% 7.95/1.47                [status(thm)],
% 7.95/1.47                [c_5709,c_35]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_6152,plain,
% 7.95/1.47      ( sP0(k1_pre_topc(sK6,sK9),sK6) = iProver_top
% 7.95/1.47      | l1_pre_topc(sK6) != iProver_top ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_6147,c_4737]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_6804,plain,
% 7.95/1.47      ( sP0(k1_pre_topc(sK6,sK9),sK6) = iProver_top ),
% 7.95/1.47      inference(global_propositional_subsumption,
% 7.95/1.47                [status(thm)],
% 7.95/1.47                [c_6152,c_35]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_8,plain,
% 7.95/1.47      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 7.95/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.95/1.47      | ~ l1_pre_topc(X0)
% 7.95/1.47      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 7.95/1.47      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 7.95/1.47      inference(cnf_transformation,[],[f91]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_219,plain,
% 7.95/1.47      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.95/1.47      | ~ l1_pre_topc(X0)
% 7.95/1.47      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 7.95/1.47      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 7.95/1.47      inference(global_propositional_subsumption,
% 7.95/1.47                [status(thm)],
% 7.95/1.47                [c_8,c_22]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_220,plain,
% 7.95/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.95/1.47      | ~ l1_pre_topc(X1)
% 7.95/1.47      | ~ v1_pre_topc(k1_pre_topc(X1,X0))
% 7.95/1.47      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 7.95/1.47      inference(renaming,[status(thm)],[c_219]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_23,plain,
% 7.95/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.95/1.47      | ~ l1_pre_topc(X1)
% 7.95/1.47      | v1_pre_topc(k1_pre_topc(X1,X0)) ),
% 7.95/1.47      inference(cnf_transformation,[],[f72]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_225,plain,
% 7.95/1.47      ( ~ l1_pre_topc(X1)
% 7.95/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.95/1.47      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 7.95/1.47      inference(global_propositional_subsumption,
% 7.95/1.47                [status(thm)],
% 7.95/1.47                [c_220,c_23]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_226,plain,
% 7.95/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.95/1.47      | ~ l1_pre_topc(X1)
% 7.95/1.47      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 7.95/1.47      inference(renaming,[status(thm)],[c_225]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_4740,plain,
% 7.95/1.47      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
% 7.95/1.47      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.95/1.47      | l1_pre_topc(X0) != iProver_top ),
% 7.95/1.47      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_6439,plain,
% 7.95/1.47      ( k2_struct_0(k1_pre_topc(sK6,sK9)) = sK9
% 7.95/1.47      | l1_pre_topc(sK6) != iProver_top ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_4742,c_4740]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_4935,plain,
% 7.95/1.47      ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0)))
% 7.95/1.47      | ~ l1_pre_topc(X0)
% 7.95/1.47      | k2_struct_0(k1_pre_topc(X0,sK9)) = sK9 ),
% 7.95/1.47      inference(instantiation,[status(thm)],[c_226]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_4937,plain,
% 7.95/1.47      ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.95/1.47      | ~ l1_pre_topc(sK6)
% 7.95/1.47      | k2_struct_0(k1_pre_topc(sK6,sK9)) = sK9 ),
% 7.95/1.47      inference(instantiation,[status(thm)],[c_4935]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_6605,plain,
% 7.95/1.47      ( k2_struct_0(k1_pre_topc(sK6,sK9)) = sK9 ),
% 7.95/1.47      inference(global_propositional_subsumption,
% 7.95/1.47                [status(thm)],
% 7.95/1.47                [c_6439,c_34,c_33,c_4937]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_6607,plain,
% 7.95/1.47      ( sP0(k1_pre_topc(sK6,sK9),X0) != iProver_top
% 7.95/1.47      | r1_tarski(sK9,k2_struct_0(X0)) = iProver_top ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_6605,c_4754]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_7240,plain,
% 7.95/1.47      ( r1_tarski(sK9,k2_struct_0(sK6)) = iProver_top ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_6804,c_6607]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_8980,plain,
% 7.95/1.47      ( k9_subset_1(k2_struct_0(sK6),X0,sK9) = k1_setfam_1(k2_tarski(X0,sK9)) ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_7240,c_4738]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_10274,plain,
% 7.95/1.47      ( k1_setfam_1(k2_tarski(k2_struct_0(sK8),sK9)) = k1_setfam_1(k2_tarski(sK9,k2_struct_0(sK8))) ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_9304,c_8980]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_5708,plain,
% 7.95/1.47      ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top
% 7.95/1.47      | l1_pre_topc(sK8) != iProver_top ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_4745,c_4753]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_978,plain,
% 7.95/1.47      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK6 != X0 | sK8 != X1 ),
% 7.95/1.47      inference(resolution_lifted,[status(thm)],[c_24,c_32]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_979,plain,
% 7.95/1.47      ( ~ l1_pre_topc(sK6) | l1_pre_topc(sK8) ),
% 7.95/1.47      inference(unflattening,[status(thm)],[c_978]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_980,plain,
% 7.95/1.47      ( l1_pre_topc(sK6) != iProver_top
% 7.95/1.47      | l1_pre_topc(sK8) = iProver_top ),
% 7.95/1.47      inference(predicate_to_equality,[status(thm)],[c_979]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_5950,plain,
% 7.95/1.47      ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top ),
% 7.95/1.47      inference(global_propositional_subsumption,
% 7.95/1.47                [status(thm)],
% 7.95/1.47                [c_5708,c_35,c_980]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_5955,plain,
% 7.95/1.47      ( sP0(k1_pre_topc(sK8,sK9),sK8) = iProver_top
% 7.95/1.47      | l1_pre_topc(sK8) != iProver_top ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_5950,c_4737]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_6798,plain,
% 7.95/1.47      ( sP0(k1_pre_topc(sK8,sK9),sK8) = iProver_top ),
% 7.95/1.47      inference(global_propositional_subsumption,
% 7.95/1.47                [status(thm)],
% 7.95/1.47                [c_5955,c_35,c_980]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_6438,plain,
% 7.95/1.47      ( k2_struct_0(k1_pre_topc(sK8,sK9)) = sK9
% 7.95/1.47      | l1_pre_topc(sK8) != iProver_top ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_4745,c_4740]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_6594,plain,
% 7.95/1.47      ( k2_struct_0(k1_pre_topc(sK8,sK9)) = sK9 ),
% 7.95/1.47      inference(global_propositional_subsumption,
% 7.95/1.47                [status(thm)],
% 7.95/1.47                [c_6438,c_35,c_980]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_6596,plain,
% 7.95/1.47      ( sP0(k1_pre_topc(sK8,sK9),X0) != iProver_top
% 7.95/1.47      | r1_tarski(sK9,k2_struct_0(X0)) = iProver_top ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_6594,c_4754]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_6861,plain,
% 7.95/1.47      ( r1_tarski(sK9,k2_struct_0(sK8)) = iProver_top ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_6798,c_6596]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_0,plain,
% 7.95/1.47      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 7.95/1.47      inference(cnf_transformation,[],[f86]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_4768,plain,
% 7.95/1.47      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 7.95/1.47      | r1_tarski(X0,X1) != iProver_top ),
% 7.95/1.47      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_8114,plain,
% 7.95/1.47      ( k1_setfam_1(k2_tarski(sK9,k2_struct_0(sK8))) = sK9 ),
% 7.95/1.47      inference(superposition,[status(thm)],[c_6861,c_4768]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_10276,plain,
% 7.95/1.47      ( k1_setfam_1(k2_tarski(k2_struct_0(sK8),sK9)) = sK9 ),
% 7.95/1.47      inference(light_normalisation,[status(thm)],[c_10274,c_8114]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_28246,plain,
% 7.95/1.47      ( v4_pre_topc(k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)),sK8) = iProver_top
% 7.95/1.47      | v4_pre_topc(sK9,X0) != iProver_top
% 7.95/1.47      | m1_pre_topc(sK8,X0) != iProver_top
% 7.95/1.47      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.95/1.47      | r1_tarski(sK9,u1_struct_0(sK8)) != iProver_top
% 7.95/1.47      | l1_pre_topc(X0) != iProver_top ),
% 7.95/1.47      inference(light_normalisation,[status(thm)],[c_28231,c_10276]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_28247,plain,
% 7.95/1.47      ( v4_pre_topc(k1_setfam_1(k2_tarski(k2_struct_0(sK8),sK9)),sK8) = iProver_top
% 7.95/1.47      | v4_pre_topc(sK9,X0) != iProver_top
% 7.95/1.47      | m1_pre_topc(sK8,X0) != iProver_top
% 7.95/1.47      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.95/1.47      | r1_tarski(sK9,u1_struct_0(sK8)) != iProver_top
% 7.95/1.47      | l1_pre_topc(X0) != iProver_top ),
% 7.95/1.47      inference(demodulation,[status(thm)],[c_28246,c_8658]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_28248,plain,
% 7.95/1.47      ( v4_pre_topc(sK9,X0) != iProver_top
% 7.95/1.47      | v4_pre_topc(sK9,sK8) = iProver_top
% 7.95/1.47      | m1_pre_topc(sK8,X0) != iProver_top
% 7.95/1.47      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.95/1.47      | r1_tarski(sK9,u1_struct_0(sK8)) != iProver_top
% 7.95/1.47      | l1_pre_topc(X0) != iProver_top ),
% 7.95/1.47      inference(light_normalisation,[status(thm)],[c_28247,c_10276]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_28259,plain,
% 7.95/1.47      ( v4_pre_topc(sK9,sK6) != iProver_top
% 7.95/1.47      | v4_pre_topc(sK9,sK8) = iProver_top
% 7.95/1.47      | m1_pre_topc(sK8,sK6) != iProver_top
% 7.95/1.47      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 7.95/1.47      | r1_tarski(sK9,u1_struct_0(sK8)) != iProver_top
% 7.95/1.47      | l1_pre_topc(sK6) != iProver_top ),
% 7.95/1.47      inference(instantiation,[status(thm)],[c_28248]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_29,negated_conjecture,
% 7.95/1.47      ( ~ v4_pre_topc(sK9,sK8) ),
% 7.95/1.47      inference(cnf_transformation,[],[f85]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_40,plain,
% 7.95/1.47      ( v4_pre_topc(sK9,sK8) != iProver_top ),
% 7.95/1.47      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_31,negated_conjecture,
% 7.95/1.47      ( v4_pre_topc(sK9,sK6) ),
% 7.95/1.47      inference(cnf_transformation,[],[f88]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_38,plain,
% 7.95/1.47      ( v4_pre_topc(sK9,sK6) = iProver_top ),
% 7.95/1.47      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_37,plain,
% 7.95/1.47      ( m1_pre_topc(sK8,sK6) = iProver_top ),
% 7.95/1.47      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(c_36,plain,
% 7.95/1.47      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 7.95/1.47      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.95/1.47  
% 7.95/1.47  cnf(contradiction,plain,
% 7.95/1.47      ( $false ),
% 7.95/1.47      inference(minisat,
% 7.95/1.47                [status(thm)],
% 7.95/1.47                [c_28259,c_5128,c_40,c_38,c_37,c_36,c_35]) ).
% 7.95/1.47  
% 7.95/1.47  
% 7.95/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 7.95/1.47  
% 7.95/1.47  ------                               Statistics
% 7.95/1.47  
% 7.95/1.47  ------ General
% 7.95/1.47  
% 7.95/1.47  abstr_ref_over_cycles:                  0
% 7.95/1.47  abstr_ref_under_cycles:                 0
% 7.95/1.47  gc_basic_clause_elim:                   0
% 7.95/1.47  forced_gc_time:                         0
% 7.95/1.47  parsing_time:                           0.011
% 7.95/1.47  unif_index_cands_time:                  0.
% 7.95/1.47  unif_index_add_time:                    0.
% 7.95/1.47  orderings_time:                         0.
% 7.95/1.47  out_proof_time:                         0.012
% 7.95/1.47  total_time:                             0.967
% 7.95/1.47  num_of_symbols:                         56
% 7.95/1.47  num_of_terms:                           34651
% 7.95/1.47  
% 7.95/1.47  ------ Preprocessing
% 7.95/1.47  
% 7.95/1.47  num_of_splits:                          0
% 7.95/1.47  num_of_split_atoms:                     0
% 7.95/1.47  num_of_reused_defs:                     0
% 7.95/1.47  num_eq_ax_congr_red:                    53
% 7.95/1.47  num_of_sem_filtered_clauses:            1
% 7.95/1.47  num_of_subtypes:                        0
% 7.95/1.47  monotx_restored_types:                  0
% 7.95/1.47  sat_num_of_epr_types:                   0
% 7.95/1.47  sat_num_of_non_cyclic_types:            0
% 7.95/1.47  sat_guarded_non_collapsed_types:        0
% 7.95/1.47  num_pure_diseq_elim:                    0
% 7.95/1.47  simp_replaced_by:                       0
% 7.95/1.47  res_preprocessed:                       168
% 7.95/1.47  prep_upred:                             0
% 7.95/1.47  prep_unflattend:                        210
% 7.95/1.47  smt_new_axioms:                         0
% 7.95/1.47  pred_elim_cands:                        8
% 7.95/1.47  pred_elim:                              1
% 7.95/1.47  pred_elim_cl:                           1
% 7.95/1.47  pred_elim_cycles:                       9
% 7.95/1.47  merged_defs:                            8
% 7.95/1.47  merged_defs_ncl:                        0
% 7.95/1.47  bin_hyper_res:                          10
% 7.95/1.47  prep_cycles:                            4
% 7.95/1.47  pred_elim_time:                         0.066
% 7.95/1.47  splitting_time:                         0.
% 7.95/1.47  sem_filter_time:                        0.
% 7.95/1.47  monotx_time:                            0.001
% 7.95/1.47  subtype_inf_time:                       0.
% 7.95/1.47  
% 7.95/1.47  ------ Problem properties
% 7.95/1.47  
% 7.95/1.47  clauses:                                34
% 7.95/1.47  conjectures:                            6
% 7.95/1.47  epr:                                    7
% 7.95/1.47  horn:                                   30
% 7.95/1.47  ground:                                 6
% 7.95/1.47  unary:                                  8
% 7.95/1.47  binary:                                 6
% 7.95/1.47  lits:                                   103
% 7.95/1.47  lits_eq:                                10
% 7.95/1.47  fd_pure:                                0
% 7.95/1.47  fd_pseudo:                              0
% 7.95/1.47  fd_cond:                                0
% 7.95/1.47  fd_pseudo_cond:                         0
% 7.95/1.47  ac_symbols:                             0
% 7.95/1.47  
% 7.95/1.47  ------ Propositional Solver
% 7.95/1.47  
% 7.95/1.47  prop_solver_calls:                      36
% 7.95/1.47  prop_fast_solver_calls:                 3044
% 7.95/1.47  smt_solver_calls:                       0
% 7.95/1.47  smt_fast_solver_calls:                  0
% 7.95/1.47  prop_num_of_clauses:                    13671
% 7.95/1.47  prop_preprocess_simplified:             25075
% 7.95/1.47  prop_fo_subsumed:                       110
% 7.95/1.47  prop_solver_time:                       0.
% 7.95/1.47  smt_solver_time:                        0.
% 7.95/1.47  smt_fast_solver_time:                   0.
% 7.95/1.47  prop_fast_solver_time:                  0.
% 7.95/1.47  prop_unsat_core_time:                   0.001
% 7.95/1.47  
% 7.95/1.47  ------ QBF
% 7.95/1.47  
% 7.95/1.47  qbf_q_res:                              0
% 7.95/1.47  qbf_num_tautologies:                    0
% 7.95/1.47  qbf_prep_cycles:                        0
% 7.95/1.47  
% 7.95/1.47  ------ BMC1
% 7.95/1.47  
% 7.95/1.47  bmc1_current_bound:                     -1
% 7.95/1.47  bmc1_last_solved_bound:                 -1
% 7.95/1.47  bmc1_unsat_core_size:                   -1
% 7.95/1.47  bmc1_unsat_core_parents_size:           -1
% 7.95/1.47  bmc1_merge_next_fun:                    0
% 7.95/1.47  bmc1_unsat_core_clauses_time:           0.
% 7.95/1.47  
% 7.95/1.47  ------ Instantiation
% 7.95/1.47  
% 7.95/1.47  inst_num_of_clauses:                    3741
% 7.95/1.47  inst_num_in_passive:                    886
% 7.95/1.47  inst_num_in_active:                     1332
% 7.95/1.47  inst_num_in_unprocessed:                1523
% 7.95/1.47  inst_num_of_loops:                      1450
% 7.95/1.47  inst_num_of_learning_restarts:          0
% 7.95/1.47  inst_num_moves_active_passive:          110
% 7.95/1.47  inst_lit_activity:                      0
% 7.95/1.47  inst_lit_activity_moves:                1
% 7.95/1.47  inst_num_tautologies:                   0
% 7.95/1.47  inst_num_prop_implied:                  0
% 7.95/1.47  inst_num_existing_simplified:           0
% 7.95/1.47  inst_num_eq_res_simplified:             0
% 7.95/1.47  inst_num_child_elim:                    0
% 7.95/1.47  inst_num_of_dismatching_blockings:      1580
% 7.95/1.47  inst_num_of_non_proper_insts:           3610
% 7.95/1.47  inst_num_of_duplicates:                 0
% 7.95/1.47  inst_inst_num_from_inst_to_res:         0
% 7.95/1.47  inst_dismatching_checking_time:         0.
% 7.95/1.47  
% 7.95/1.47  ------ Resolution
% 7.95/1.47  
% 7.95/1.47  res_num_of_clauses:                     0
% 7.95/1.47  res_num_in_passive:                     0
% 7.95/1.47  res_num_in_active:                      0
% 7.95/1.47  res_num_of_loops:                       172
% 7.95/1.47  res_forward_subset_subsumed:            262
% 7.95/1.47  res_backward_subset_subsumed:           0
% 7.95/1.47  res_forward_subsumed:                   0
% 7.95/1.47  res_backward_subsumed:                  0
% 7.95/1.47  res_forward_subsumption_resolution:     0
% 7.95/1.47  res_backward_subsumption_resolution:    0
% 7.95/1.47  res_clause_to_clause_subsumption:       4826
% 7.95/1.47  res_orphan_elimination:                 0
% 7.95/1.47  res_tautology_del:                      166
% 7.95/1.47  res_num_eq_res_simplified:              0
% 7.95/1.47  res_num_sel_changes:                    0
% 7.95/1.47  res_moves_from_active_to_pass:          0
% 7.95/1.47  
% 7.95/1.47  ------ Superposition
% 7.95/1.47  
% 7.95/1.47  sup_time_total:                         0.
% 7.95/1.47  sup_time_generating:                    0.
% 7.95/1.47  sup_time_sim_full:                      0.
% 7.95/1.47  sup_time_sim_immed:                     0.
% 7.95/1.47  
% 7.95/1.47  sup_num_of_clauses:                     824
% 7.95/1.47  sup_num_in_active:                      287
% 7.95/1.47  sup_num_in_passive:                     537
% 7.95/1.47  sup_num_of_loops:                       288
% 7.95/1.47  sup_fw_superposition:                   544
% 7.95/1.47  sup_bw_superposition:                   588
% 7.95/1.47  sup_immediate_simplified:               403
% 7.95/1.47  sup_given_eliminated:                   0
% 7.95/1.47  comparisons_done:                       0
% 7.95/1.47  comparisons_avoided:                    180
% 7.95/1.47  
% 7.95/1.47  ------ Simplifications
% 7.95/1.47  
% 7.95/1.47  
% 7.95/1.47  sim_fw_subset_subsumed:                 30
% 7.95/1.47  sim_bw_subset_subsumed:                 1
% 7.95/1.47  sim_fw_subsumed:                        81
% 7.95/1.47  sim_bw_subsumed:                        2
% 7.95/1.47  sim_fw_subsumption_res:                 0
% 7.95/1.47  sim_bw_subsumption_res:                 0
% 7.95/1.47  sim_tautology_del:                      127
% 7.95/1.47  sim_eq_tautology_del:                   16
% 7.95/1.47  sim_eq_res_simp:                        0
% 7.95/1.47  sim_fw_demodulated:                     8
% 7.95/1.47  sim_bw_demodulated:                     1
% 7.95/1.47  sim_light_normalised:                   360
% 7.95/1.47  sim_joinable_taut:                      0
% 7.95/1.47  sim_joinable_simp:                      0
% 7.95/1.47  sim_ac_normalised:                      0
% 7.95/1.47  sim_smt_subsumption:                    0
% 7.95/1.47  
%------------------------------------------------------------------------------
