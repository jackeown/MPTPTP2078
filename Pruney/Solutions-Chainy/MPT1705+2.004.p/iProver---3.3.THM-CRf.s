%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:44 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  183 (2957 expanded)
%              Number of clauses        :  105 ( 773 expanded)
%              Number of leaves         :   17 ( 744 expanded)
%              Depth                    :   22
%              Number of atoms          :  896 (28945 expanded)
%              Number of equality atoms :  277 (3273 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f31,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f18,f31])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X1] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r1_tarski(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
            & r1_tarski(sK3(X0),u1_pre_topc(X0))
            & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f71,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2) )
               => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                 => ( ( m1_pre_topc(X1,X0)
                      & v1_tsep_1(X1,X0) )
                  <=> ( m1_pre_topc(X2,X0)
                      & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_tsep_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_tsep_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_tsep_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_tsep_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,X0)
            | ~ v1_tsep_1(X2,X0)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( ( m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0) )
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
          & l1_pre_topc(X2)
          & v2_pre_topc(X2) )
     => ( ( ~ m1_pre_topc(sK6,X0)
          | ~ v1_tsep_1(sK6,X0)
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
        & ( ( m1_pre_topc(sK6,X0)
            & v1_tsep_1(sK6,X0) )
          | ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) ) )
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = sK6
        & l1_pre_topc(sK6)
        & v2_pre_topc(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_tsep_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_tsep_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0)
              | ~ m1_pre_topc(sK5,X0)
              | ~ v1_tsep_1(sK5,X0) )
            & ( ( m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0) )
              | ( m1_pre_topc(sK5,X0)
                & v1_tsep_1(sK5,X0) ) )
            & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = X2
            & l1_pre_topc(X2)
            & v2_pre_topc(X2) )
        & l1_pre_topc(sK5)
        & v2_pre_topc(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,X0)
                  | ~ v1_tsep_1(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) )
                  | ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) ) )
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                & l1_pre_topc(X2)
                & v2_pre_topc(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,sK4)
                | ~ v1_tsep_1(X2,sK4)
                | ~ m1_pre_topc(X1,sK4)
                | ~ v1_tsep_1(X1,sK4) )
              & ( ( m1_pre_topc(X2,sK4)
                  & v1_tsep_1(X2,sK4) )
                | ( m1_pre_topc(X1,sK4)
                  & v1_tsep_1(X1,sK4) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ( ~ m1_pre_topc(sK6,sK4)
      | ~ v1_tsep_1(sK6,sK4)
      | ~ m1_pre_topc(sK5,sK4)
      | ~ v1_tsep_1(sK5,sK4) )
    & ( ( m1_pre_topc(sK6,sK4)
        & v1_tsep_1(sK6,sK4) )
      | ( m1_pre_topc(sK5,sK4)
        & v1_tsep_1(sK5,sK4) ) )
    & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f53,f56,f55,f54])).

fof(f97,plain,(
    g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6 ),
    inference(cnf_transformation,[],[f57])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f93,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f95,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f96,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f106,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f101,plain,
    ( m1_pre_topc(sK6,sK4)
    | m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f102,plain,
    ( ~ m1_pre_topc(sK6,sK4)
    | ~ v1_tsep_1(sK6,sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | ~ v1_tsep_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f98,plain,
    ( v1_tsep_1(sK6,sK4)
    | v1_tsep_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_18,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2853,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2867,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2870,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2867,c_3])).

cnf(c_19,plain,
    ( v3_pre_topc(X0,X1)
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2852,plain,
    ( v3_pre_topc(X0,X1) = iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4640,plain,
    ( v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2870,c_2852])).

cnf(c_6781,plain,
    ( v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2853,c_4640])).

cnf(c_38,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_23,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2848,plain,
    ( v3_pre_topc(X0,X1) = iProver_top
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5391,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v3_pre_topc(X0,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_38,c_2848])).

cnf(c_5392,plain,
    ( v3_pre_topc(X0,sK5) = iProver_top
    | v3_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5391,c_38])).

cnf(c_42,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_47,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_48,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_5412,plain,
    ( v3_pre_topc(X0,sK5) = iProver_top
    | v3_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5392,c_47,c_48])).

cnf(c_5422,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK5) = iProver_top
    | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2870,c_5412])).

cnf(c_6790,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK5) = iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6781,c_5422])).

cnf(c_40,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_49,plain,
    ( v2_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_50,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_7030,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6790,c_49,c_50])).

cnf(c_32,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2843,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_25,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2846,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4773,plain,
    ( v3_pre_topc(X0,sK5) != iProver_top
    | v3_pre_topc(X0,sK6) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_38,c_2846])).

cnf(c_4852,plain,
    ( v3_pre_topc(X0,sK5) != iProver_top
    | v3_pre_topc(X0,sK6) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4773,c_47,c_48])).

cnf(c_4861,plain,
    ( m1_pre_topc(X0,sK5) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK5) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK6) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2843,c_4852])).

cnf(c_5024,plain,
    ( v3_pre_topc(u1_struct_0(X0),sK6) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK5) != iProver_top
    | m1_pre_topc(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4861,c_48])).

cnf(c_5025,plain,
    ( m1_pre_topc(X0,sK5) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK5) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_5024])).

cnf(c_7035,plain,
    ( m1_pre_topc(sK6,sK5) != iProver_top
    | v3_pre_topc(u1_struct_0(sK6),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_7030,c_5025])).

cnf(c_4862,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK5) != iProver_top
    | v3_pre_topc(u1_struct_0(sK5),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2870,c_4852])).

cnf(c_6789,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK6) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6781,c_4862])).

cnf(c_6917,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6789,c_47,c_48])).

cnf(c_5421,plain,
    ( m1_pre_topc(X0,sK6) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK5) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2843,c_5412])).

cnf(c_5654,plain,
    ( v3_pre_topc(u1_struct_0(X0),sK6) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK5) = iProver_top
    | m1_pre_topc(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5421,c_50])).

cnf(c_5655,plain,
    ( m1_pre_topc(X0,sK6) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK5) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_5654])).

cnf(c_6922,plain,
    ( m1_pre_topc(sK5,sK6) != iProver_top
    | v3_pre_topc(u1_struct_0(sK5),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_6917,c_5655])).

cnf(c_22,plain,
    ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2849,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5846,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_38,c_2849])).

cnf(c_5847,plain,
    ( v3_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5846,c_38])).

cnf(c_5965,plain,
    ( v3_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5847,c_47,c_48])).

cnf(c_5975,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2870,c_5965])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2865,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6206,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
    | r1_tarski(u1_struct_0(sK6),u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5975,c_2865])).

cnf(c_24,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2847,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5183,plain,
    ( v3_pre_topc(X0,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_38,c_2847])).

cnf(c_5197,plain,
    ( v3_pre_topc(X0,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5183,c_47,c_48])).

cnf(c_5207,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK5) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2870,c_5197])).

cnf(c_5521,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK5) != iProver_top
    | r1_tarski(u1_struct_0(sK5),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5207,c_2865])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2869,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5833,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK5)
    | v3_pre_topc(u1_struct_0(sK5),sK5) != iProver_top
    | r1_tarski(u1_struct_0(sK6),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5521,c_2869])).

cnf(c_7372,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK5)
    | v3_pre_topc(u1_struct_0(sK5),sK5) != iProver_top
    | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6206,c_5833])).

cnf(c_8578,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK5)
    | m1_pre_topc(sK5,sK6) != iProver_top
    | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6922,c_7372])).

cnf(c_8575,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK5)
    | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6781,c_7372])).

cnf(c_8582,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK5)
    | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8578,c_47,c_48,c_8575])).

cnf(c_8590,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK5)
    | m1_pre_topc(sK6,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7035,c_8582])).

cnf(c_8587,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK5)
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6781,c_8582])).

cnf(c_8661,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8590,c_49,c_50,c_8587])).

cnf(c_30,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_247,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30,c_32])).

cnf(c_248,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_247])).

cnf(c_2830,plain,
    ( v1_tsep_1(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_248])).

cnf(c_8731,plain,
    ( v1_tsep_1(sK5,X0) = iProver_top
    | m1_pre_topc(sK5,X0) != iProver_top
    | v3_pre_topc(u1_struct_0(sK6),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8661,c_2830])).

cnf(c_8776,plain,
    ( v1_tsep_1(sK5,sK4) = iProver_top
    | m1_pre_topc(sK5,sK4) != iProver_top
    | v3_pre_topc(u1_struct_0(sK6),sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8731])).

cnf(c_31,plain,
    ( ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_240,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31,c_32])).

cnf(c_241,plain,
    ( ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_240])).

cnf(c_2831,plain,
    ( v1_tsep_1(X0,X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_241])).

cnf(c_8730,plain,
    ( v1_tsep_1(sK5,X0) != iProver_top
    | m1_pre_topc(sK5,X0) != iProver_top
    | v3_pre_topc(u1_struct_0(sK6),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8661,c_2831])).

cnf(c_8773,plain,
    ( v1_tsep_1(sK5,sK4) != iProver_top
    | m1_pre_topc(sK5,sK4) != iProver_top
    | v3_pre_topc(u1_struct_0(sK6),sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8730])).

cnf(c_5134,plain,
    ( ~ v1_tsep_1(sK6,sK4)
    | ~ m1_pre_topc(sK6,sK4)
    | v3_pre_topc(u1_struct_0(sK6),sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_241])).

cnf(c_5135,plain,
    ( v1_tsep_1(sK6,sK4) != iProver_top
    | m1_pre_topc(sK6,sK4) != iProver_top
    | v3_pre_topc(u1_struct_0(sK6),sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5134])).

cnf(c_28,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2844,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4535,plain,
    ( m1_pre_topc(sK5,X0) = iProver_top
    | m1_pre_topc(sK6,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_38,c_2844])).

cnf(c_4536,plain,
    ( m1_pre_topc(sK5,X0) = iProver_top
    | m1_pre_topc(sK6,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4535,c_38])).

cnf(c_4538,plain,
    ( m1_pre_topc(sK5,sK4) = iProver_top
    | m1_pre_topc(sK6,sK4) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4536])).

cnf(c_34,negated_conjecture,
    ( m1_pre_topc(sK5,sK4)
    | m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2841,plain,
    ( m1_pre_topc(sK5,sK4) = iProver_top
    | m1_pre_topc(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_26,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2845,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4143,plain,
    ( m1_pre_topc(sK5,X0) != iProver_top
    | m1_pre_topc(sK6,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_38,c_2845])).

cnf(c_4152,plain,
    ( m1_pre_topc(sK6,sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2841,c_4143])).

cnf(c_2924,plain,
    ( v1_tsep_1(sK6,sK4)
    | ~ m1_pre_topc(sK6,sK4)
    | ~ v3_pre_topc(u1_struct_0(sK6),sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_2925,plain,
    ( v1_tsep_1(sK6,sK4) = iProver_top
    | m1_pre_topc(sK6,sK4) != iProver_top
    | v3_pre_topc(u1_struct_0(sK6),sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2924])).

cnf(c_33,negated_conjecture,
    ( ~ v1_tsep_1(sK5,sK4)
    | ~ v1_tsep_1(sK6,sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | ~ m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_55,plain,
    ( v1_tsep_1(sK5,sK4) != iProver_top
    | v1_tsep_1(sK6,sK4) != iProver_top
    | m1_pre_topc(sK5,sK4) != iProver_top
    | m1_pre_topc(sK6,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_37,negated_conjecture,
    ( v1_tsep_1(sK5,sK4)
    | v1_tsep_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_51,plain,
    ( v1_tsep_1(sK5,sK4) = iProver_top
    | v1_tsep_1(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_43,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_46,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_44,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_45,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8776,c_8773,c_5135,c_4538,c_4152,c_2925,c_55,c_51,c_50,c_49,c_48,c_47,c_46,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.70/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.03  
% 3.70/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.70/1.03  
% 3.70/1.03  ------  iProver source info
% 3.70/1.03  
% 3.70/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.70/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.70/1.03  git: non_committed_changes: false
% 3.70/1.03  git: last_make_outside_of_git: false
% 3.70/1.03  
% 3.70/1.03  ------ 
% 3.70/1.03  
% 3.70/1.03  ------ Input Options
% 3.70/1.03  
% 3.70/1.03  --out_options                           all
% 3.70/1.03  --tptp_safe_out                         true
% 3.70/1.03  --problem_path                          ""
% 3.70/1.03  --include_path                          ""
% 3.70/1.03  --clausifier                            res/vclausify_rel
% 3.70/1.03  --clausifier_options                    ""
% 3.70/1.03  --stdin                                 false
% 3.70/1.03  --stats_out                             all
% 3.70/1.03  
% 3.70/1.03  ------ General Options
% 3.70/1.03  
% 3.70/1.03  --fof                                   false
% 3.70/1.03  --time_out_real                         305.
% 3.70/1.03  --time_out_virtual                      -1.
% 3.70/1.03  --symbol_type_check                     false
% 3.70/1.03  --clausify_out                          false
% 3.70/1.03  --sig_cnt_out                           false
% 3.70/1.03  --trig_cnt_out                          false
% 3.70/1.03  --trig_cnt_out_tolerance                1.
% 3.70/1.03  --trig_cnt_out_sk_spl                   false
% 3.70/1.03  --abstr_cl_out                          false
% 3.70/1.03  
% 3.70/1.03  ------ Global Options
% 3.70/1.03  
% 3.70/1.03  --schedule                              default
% 3.70/1.03  --add_important_lit                     false
% 3.70/1.03  --prop_solver_per_cl                    1000
% 3.70/1.03  --min_unsat_core                        false
% 3.70/1.03  --soft_assumptions                      false
% 3.70/1.03  --soft_lemma_size                       3
% 3.70/1.03  --prop_impl_unit_size                   0
% 3.70/1.03  --prop_impl_unit                        []
% 3.70/1.03  --share_sel_clauses                     true
% 3.70/1.03  --reset_solvers                         false
% 3.70/1.03  --bc_imp_inh                            [conj_cone]
% 3.70/1.03  --conj_cone_tolerance                   3.
% 3.70/1.03  --extra_neg_conj                        none
% 3.70/1.03  --large_theory_mode                     true
% 3.70/1.03  --prolific_symb_bound                   200
% 3.70/1.03  --lt_threshold                          2000
% 3.70/1.03  --clause_weak_htbl                      true
% 3.70/1.03  --gc_record_bc_elim                     false
% 3.70/1.03  
% 3.70/1.03  ------ Preprocessing Options
% 3.70/1.03  
% 3.70/1.03  --preprocessing_flag                    true
% 3.70/1.03  --time_out_prep_mult                    0.1
% 3.70/1.03  --splitting_mode                        input
% 3.70/1.03  --splitting_grd                         true
% 3.70/1.03  --splitting_cvd                         false
% 3.70/1.03  --splitting_cvd_svl                     false
% 3.70/1.03  --splitting_nvd                         32
% 3.70/1.03  --sub_typing                            true
% 3.70/1.03  --prep_gs_sim                           true
% 3.70/1.03  --prep_unflatten                        true
% 3.70/1.03  --prep_res_sim                          true
% 3.70/1.03  --prep_upred                            true
% 3.70/1.03  --prep_sem_filter                       exhaustive
% 3.70/1.03  --prep_sem_filter_out                   false
% 3.70/1.03  --pred_elim                             true
% 3.70/1.03  --res_sim_input                         true
% 3.70/1.03  --eq_ax_congr_red                       true
% 3.70/1.03  --pure_diseq_elim                       true
% 3.70/1.03  --brand_transform                       false
% 3.70/1.03  --non_eq_to_eq                          false
% 3.70/1.03  --prep_def_merge                        true
% 3.70/1.03  --prep_def_merge_prop_impl              false
% 3.70/1.03  --prep_def_merge_mbd                    true
% 3.70/1.03  --prep_def_merge_tr_red                 false
% 3.70/1.03  --prep_def_merge_tr_cl                  false
% 3.70/1.03  --smt_preprocessing                     true
% 3.70/1.03  --smt_ac_axioms                         fast
% 3.70/1.03  --preprocessed_out                      false
% 3.70/1.03  --preprocessed_stats                    false
% 3.70/1.03  
% 3.70/1.03  ------ Abstraction refinement Options
% 3.70/1.03  
% 3.70/1.03  --abstr_ref                             []
% 3.70/1.03  --abstr_ref_prep                        false
% 3.70/1.03  --abstr_ref_until_sat                   false
% 3.70/1.03  --abstr_ref_sig_restrict                funpre
% 3.70/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/1.03  --abstr_ref_under                       []
% 3.70/1.03  
% 3.70/1.03  ------ SAT Options
% 3.70/1.03  
% 3.70/1.03  --sat_mode                              false
% 3.70/1.03  --sat_fm_restart_options                ""
% 3.70/1.03  --sat_gr_def                            false
% 3.70/1.03  --sat_epr_types                         true
% 3.70/1.03  --sat_non_cyclic_types                  false
% 3.70/1.03  --sat_finite_models                     false
% 3.70/1.03  --sat_fm_lemmas                         false
% 3.70/1.03  --sat_fm_prep                           false
% 3.70/1.03  --sat_fm_uc_incr                        true
% 3.70/1.03  --sat_out_model                         small
% 3.70/1.03  --sat_out_clauses                       false
% 3.70/1.03  
% 3.70/1.03  ------ QBF Options
% 3.70/1.03  
% 3.70/1.03  --qbf_mode                              false
% 3.70/1.03  --qbf_elim_univ                         false
% 3.70/1.03  --qbf_dom_inst                          none
% 3.70/1.03  --qbf_dom_pre_inst                      false
% 3.70/1.03  --qbf_sk_in                             false
% 3.70/1.03  --qbf_pred_elim                         true
% 3.70/1.03  --qbf_split                             512
% 3.70/1.03  
% 3.70/1.03  ------ BMC1 Options
% 3.70/1.03  
% 3.70/1.03  --bmc1_incremental                      false
% 3.70/1.03  --bmc1_axioms                           reachable_all
% 3.70/1.03  --bmc1_min_bound                        0
% 3.70/1.03  --bmc1_max_bound                        -1
% 3.70/1.03  --bmc1_max_bound_default                -1
% 3.70/1.03  --bmc1_symbol_reachability              true
% 3.70/1.03  --bmc1_property_lemmas                  false
% 3.70/1.03  --bmc1_k_induction                      false
% 3.70/1.03  --bmc1_non_equiv_states                 false
% 3.70/1.03  --bmc1_deadlock                         false
% 3.70/1.03  --bmc1_ucm                              false
% 3.70/1.03  --bmc1_add_unsat_core                   none
% 3.70/1.03  --bmc1_unsat_core_children              false
% 3.70/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/1.03  --bmc1_out_stat                         full
% 3.70/1.03  --bmc1_ground_init                      false
% 3.70/1.03  --bmc1_pre_inst_next_state              false
% 3.70/1.03  --bmc1_pre_inst_state                   false
% 3.70/1.03  --bmc1_pre_inst_reach_state             false
% 3.70/1.03  --bmc1_out_unsat_core                   false
% 3.70/1.03  --bmc1_aig_witness_out                  false
% 3.70/1.03  --bmc1_verbose                          false
% 3.70/1.03  --bmc1_dump_clauses_tptp                false
% 3.70/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.70/1.03  --bmc1_dump_file                        -
% 3.70/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.70/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.70/1.03  --bmc1_ucm_extend_mode                  1
% 3.70/1.03  --bmc1_ucm_init_mode                    2
% 3.70/1.03  --bmc1_ucm_cone_mode                    none
% 3.70/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.70/1.03  --bmc1_ucm_relax_model                  4
% 3.70/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.70/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/1.03  --bmc1_ucm_layered_model                none
% 3.70/1.03  --bmc1_ucm_max_lemma_size               10
% 3.70/1.03  
% 3.70/1.03  ------ AIG Options
% 3.70/1.03  
% 3.70/1.03  --aig_mode                              false
% 3.70/1.03  
% 3.70/1.03  ------ Instantiation Options
% 3.70/1.03  
% 3.70/1.03  --instantiation_flag                    true
% 3.70/1.03  --inst_sos_flag                         true
% 3.70/1.03  --inst_sos_phase                        true
% 3.70/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/1.03  --inst_lit_sel_side                     num_symb
% 3.70/1.03  --inst_solver_per_active                1400
% 3.70/1.03  --inst_solver_calls_frac                1.
% 3.70/1.03  --inst_passive_queue_type               priority_queues
% 3.70/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/1.03  --inst_passive_queues_freq              [25;2]
% 3.70/1.03  --inst_dismatching                      true
% 3.70/1.03  --inst_eager_unprocessed_to_passive     true
% 3.70/1.03  --inst_prop_sim_given                   true
% 3.70/1.03  --inst_prop_sim_new                     false
% 3.70/1.03  --inst_subs_new                         false
% 3.70/1.03  --inst_eq_res_simp                      false
% 3.70/1.03  --inst_subs_given                       false
% 3.70/1.03  --inst_orphan_elimination               true
% 3.70/1.03  --inst_learning_loop_flag               true
% 3.70/1.03  --inst_learning_start                   3000
% 3.70/1.03  --inst_learning_factor                  2
% 3.70/1.03  --inst_start_prop_sim_after_learn       3
% 3.70/1.03  --inst_sel_renew                        solver
% 3.70/1.03  --inst_lit_activity_flag                true
% 3.70/1.03  --inst_restr_to_given                   false
% 3.70/1.03  --inst_activity_threshold               500
% 3.70/1.03  --inst_out_proof                        true
% 3.70/1.03  
% 3.70/1.03  ------ Resolution Options
% 3.70/1.03  
% 3.70/1.03  --resolution_flag                       true
% 3.70/1.03  --res_lit_sel                           adaptive
% 3.70/1.03  --res_lit_sel_side                      none
% 3.70/1.03  --res_ordering                          kbo
% 3.70/1.03  --res_to_prop_solver                    active
% 3.70/1.03  --res_prop_simpl_new                    false
% 3.70/1.03  --res_prop_simpl_given                  true
% 3.70/1.03  --res_passive_queue_type                priority_queues
% 3.70/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/1.03  --res_passive_queues_freq               [15;5]
% 3.70/1.03  --res_forward_subs                      full
% 3.70/1.03  --res_backward_subs                     full
% 3.70/1.03  --res_forward_subs_resolution           true
% 3.70/1.03  --res_backward_subs_resolution          true
% 3.70/1.03  --res_orphan_elimination                true
% 3.70/1.03  --res_time_limit                        2.
% 3.70/1.03  --res_out_proof                         true
% 3.70/1.03  
% 3.70/1.03  ------ Superposition Options
% 3.70/1.03  
% 3.70/1.03  --superposition_flag                    true
% 3.70/1.03  --sup_passive_queue_type                priority_queues
% 3.70/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.70/1.03  --demod_completeness_check              fast
% 3.70/1.03  --demod_use_ground                      true
% 3.70/1.03  --sup_to_prop_solver                    passive
% 3.70/1.03  --sup_prop_simpl_new                    true
% 3.70/1.03  --sup_prop_simpl_given                  true
% 3.70/1.03  --sup_fun_splitting                     true
% 3.70/1.03  --sup_smt_interval                      50000
% 3.70/1.03  
% 3.70/1.03  ------ Superposition Simplification Setup
% 3.70/1.03  
% 3.70/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.70/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.70/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.70/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.70/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.70/1.03  --sup_immed_triv                        [TrivRules]
% 3.70/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.03  --sup_immed_bw_main                     []
% 3.70/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.70/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.03  --sup_input_bw                          []
% 3.70/1.03  
% 3.70/1.03  ------ Combination Options
% 3.70/1.03  
% 3.70/1.03  --comb_res_mult                         3
% 3.70/1.03  --comb_sup_mult                         2
% 3.70/1.03  --comb_inst_mult                        10
% 3.70/1.03  
% 3.70/1.03  ------ Debug Options
% 3.70/1.03  
% 3.70/1.03  --dbg_backtrace                         false
% 3.70/1.03  --dbg_dump_prop_clauses                 false
% 3.70/1.03  --dbg_dump_prop_clauses_file            -
% 3.70/1.03  --dbg_out_stat                          false
% 3.70/1.03  ------ Parsing...
% 3.70/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.70/1.03  
% 3.70/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.70/1.03  
% 3.70/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.70/1.03  
% 3.70/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/1.03  ------ Proving...
% 3.70/1.03  ------ Problem Properties 
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  clauses                                 42
% 3.70/1.03  conjectures                             12
% 3.70/1.03  EPR                                     15
% 3.70/1.03  Horn                                    32
% 3.70/1.03  unary                                   10
% 3.70/1.03  binary                                  11
% 3.70/1.03  lits                                    125
% 3.70/1.03  lits eq                                 3
% 3.70/1.03  fd_pure                                 0
% 3.70/1.03  fd_pseudo                               0
% 3.70/1.03  fd_cond                                 0
% 3.70/1.03  fd_pseudo_cond                          1
% 3.70/1.03  AC symbols                              0
% 3.70/1.03  
% 3.70/1.03  ------ Schedule dynamic 5 is on 
% 3.70/1.03  
% 3.70/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  ------ 
% 3.70/1.03  Current options:
% 3.70/1.03  ------ 
% 3.70/1.03  
% 3.70/1.03  ------ Input Options
% 3.70/1.03  
% 3.70/1.03  --out_options                           all
% 3.70/1.03  --tptp_safe_out                         true
% 3.70/1.03  --problem_path                          ""
% 3.70/1.03  --include_path                          ""
% 3.70/1.03  --clausifier                            res/vclausify_rel
% 3.70/1.03  --clausifier_options                    ""
% 3.70/1.03  --stdin                                 false
% 3.70/1.03  --stats_out                             all
% 3.70/1.03  
% 3.70/1.03  ------ General Options
% 3.70/1.03  
% 3.70/1.03  --fof                                   false
% 3.70/1.03  --time_out_real                         305.
% 3.70/1.03  --time_out_virtual                      -1.
% 3.70/1.03  --symbol_type_check                     false
% 3.70/1.03  --clausify_out                          false
% 3.70/1.03  --sig_cnt_out                           false
% 3.70/1.03  --trig_cnt_out                          false
% 3.70/1.03  --trig_cnt_out_tolerance                1.
% 3.70/1.03  --trig_cnt_out_sk_spl                   false
% 3.70/1.03  --abstr_cl_out                          false
% 3.70/1.03  
% 3.70/1.03  ------ Global Options
% 3.70/1.03  
% 3.70/1.03  --schedule                              default
% 3.70/1.03  --add_important_lit                     false
% 3.70/1.03  --prop_solver_per_cl                    1000
% 3.70/1.03  --min_unsat_core                        false
% 3.70/1.03  --soft_assumptions                      false
% 3.70/1.03  --soft_lemma_size                       3
% 3.70/1.03  --prop_impl_unit_size                   0
% 3.70/1.03  --prop_impl_unit                        []
% 3.70/1.03  --share_sel_clauses                     true
% 3.70/1.03  --reset_solvers                         false
% 3.70/1.03  --bc_imp_inh                            [conj_cone]
% 3.70/1.03  --conj_cone_tolerance                   3.
% 3.70/1.03  --extra_neg_conj                        none
% 3.70/1.03  --large_theory_mode                     true
% 3.70/1.03  --prolific_symb_bound                   200
% 3.70/1.03  --lt_threshold                          2000
% 3.70/1.03  --clause_weak_htbl                      true
% 3.70/1.03  --gc_record_bc_elim                     false
% 3.70/1.03  
% 3.70/1.03  ------ Preprocessing Options
% 3.70/1.03  
% 3.70/1.03  --preprocessing_flag                    true
% 3.70/1.03  --time_out_prep_mult                    0.1
% 3.70/1.03  --splitting_mode                        input
% 3.70/1.03  --splitting_grd                         true
% 3.70/1.03  --splitting_cvd                         false
% 3.70/1.03  --splitting_cvd_svl                     false
% 3.70/1.03  --splitting_nvd                         32
% 3.70/1.03  --sub_typing                            true
% 3.70/1.03  --prep_gs_sim                           true
% 3.70/1.03  --prep_unflatten                        true
% 3.70/1.03  --prep_res_sim                          true
% 3.70/1.03  --prep_upred                            true
% 3.70/1.03  --prep_sem_filter                       exhaustive
% 3.70/1.03  --prep_sem_filter_out                   false
% 3.70/1.03  --pred_elim                             true
% 3.70/1.03  --res_sim_input                         true
% 3.70/1.03  --eq_ax_congr_red                       true
% 3.70/1.03  --pure_diseq_elim                       true
% 3.70/1.03  --brand_transform                       false
% 3.70/1.03  --non_eq_to_eq                          false
% 3.70/1.03  --prep_def_merge                        true
% 3.70/1.03  --prep_def_merge_prop_impl              false
% 3.70/1.03  --prep_def_merge_mbd                    true
% 3.70/1.03  --prep_def_merge_tr_red                 false
% 3.70/1.03  --prep_def_merge_tr_cl                  false
% 3.70/1.03  --smt_preprocessing                     true
% 3.70/1.03  --smt_ac_axioms                         fast
% 3.70/1.03  --preprocessed_out                      false
% 3.70/1.03  --preprocessed_stats                    false
% 3.70/1.03  
% 3.70/1.03  ------ Abstraction refinement Options
% 3.70/1.03  
% 3.70/1.03  --abstr_ref                             []
% 3.70/1.03  --abstr_ref_prep                        false
% 3.70/1.03  --abstr_ref_until_sat                   false
% 3.70/1.03  --abstr_ref_sig_restrict                funpre
% 3.70/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/1.03  --abstr_ref_under                       []
% 3.70/1.03  
% 3.70/1.03  ------ SAT Options
% 3.70/1.03  
% 3.70/1.03  --sat_mode                              false
% 3.70/1.03  --sat_fm_restart_options                ""
% 3.70/1.03  --sat_gr_def                            false
% 3.70/1.03  --sat_epr_types                         true
% 3.70/1.03  --sat_non_cyclic_types                  false
% 3.70/1.03  --sat_finite_models                     false
% 3.70/1.03  --sat_fm_lemmas                         false
% 3.70/1.03  --sat_fm_prep                           false
% 3.70/1.03  --sat_fm_uc_incr                        true
% 3.70/1.03  --sat_out_model                         small
% 3.70/1.03  --sat_out_clauses                       false
% 3.70/1.03  
% 3.70/1.03  ------ QBF Options
% 3.70/1.03  
% 3.70/1.03  --qbf_mode                              false
% 3.70/1.03  --qbf_elim_univ                         false
% 3.70/1.03  --qbf_dom_inst                          none
% 3.70/1.03  --qbf_dom_pre_inst                      false
% 3.70/1.03  --qbf_sk_in                             false
% 3.70/1.03  --qbf_pred_elim                         true
% 3.70/1.03  --qbf_split                             512
% 3.70/1.03  
% 3.70/1.03  ------ BMC1 Options
% 3.70/1.03  
% 3.70/1.03  --bmc1_incremental                      false
% 3.70/1.03  --bmc1_axioms                           reachable_all
% 3.70/1.03  --bmc1_min_bound                        0
% 3.70/1.03  --bmc1_max_bound                        -1
% 3.70/1.03  --bmc1_max_bound_default                -1
% 3.70/1.03  --bmc1_symbol_reachability              true
% 3.70/1.03  --bmc1_property_lemmas                  false
% 3.70/1.03  --bmc1_k_induction                      false
% 3.70/1.03  --bmc1_non_equiv_states                 false
% 3.70/1.03  --bmc1_deadlock                         false
% 3.70/1.03  --bmc1_ucm                              false
% 3.70/1.03  --bmc1_add_unsat_core                   none
% 3.70/1.03  --bmc1_unsat_core_children              false
% 3.70/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/1.03  --bmc1_out_stat                         full
% 3.70/1.03  --bmc1_ground_init                      false
% 3.70/1.03  --bmc1_pre_inst_next_state              false
% 3.70/1.03  --bmc1_pre_inst_state                   false
% 3.70/1.03  --bmc1_pre_inst_reach_state             false
% 3.70/1.03  --bmc1_out_unsat_core                   false
% 3.70/1.03  --bmc1_aig_witness_out                  false
% 3.70/1.03  --bmc1_verbose                          false
% 3.70/1.03  --bmc1_dump_clauses_tptp                false
% 3.70/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.70/1.03  --bmc1_dump_file                        -
% 3.70/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.70/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.70/1.03  --bmc1_ucm_extend_mode                  1
% 3.70/1.03  --bmc1_ucm_init_mode                    2
% 3.70/1.03  --bmc1_ucm_cone_mode                    none
% 3.70/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.70/1.03  --bmc1_ucm_relax_model                  4
% 3.70/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.70/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/1.03  --bmc1_ucm_layered_model                none
% 3.70/1.03  --bmc1_ucm_max_lemma_size               10
% 3.70/1.03  
% 3.70/1.03  ------ AIG Options
% 3.70/1.03  
% 3.70/1.03  --aig_mode                              false
% 3.70/1.03  
% 3.70/1.03  ------ Instantiation Options
% 3.70/1.03  
% 3.70/1.03  --instantiation_flag                    true
% 3.70/1.03  --inst_sos_flag                         true
% 3.70/1.03  --inst_sos_phase                        true
% 3.70/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/1.03  --inst_lit_sel_side                     none
% 3.70/1.03  --inst_solver_per_active                1400
% 3.70/1.03  --inst_solver_calls_frac                1.
% 3.70/1.03  --inst_passive_queue_type               priority_queues
% 3.70/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/1.03  --inst_passive_queues_freq              [25;2]
% 3.70/1.03  --inst_dismatching                      true
% 3.70/1.03  --inst_eager_unprocessed_to_passive     true
% 3.70/1.03  --inst_prop_sim_given                   true
% 3.70/1.03  --inst_prop_sim_new                     false
% 3.70/1.03  --inst_subs_new                         false
% 3.70/1.03  --inst_eq_res_simp                      false
% 3.70/1.03  --inst_subs_given                       false
% 3.70/1.03  --inst_orphan_elimination               true
% 3.70/1.03  --inst_learning_loop_flag               true
% 3.70/1.03  --inst_learning_start                   3000
% 3.70/1.03  --inst_learning_factor                  2
% 3.70/1.03  --inst_start_prop_sim_after_learn       3
% 3.70/1.03  --inst_sel_renew                        solver
% 3.70/1.03  --inst_lit_activity_flag                true
% 3.70/1.03  --inst_restr_to_given                   false
% 3.70/1.03  --inst_activity_threshold               500
% 3.70/1.03  --inst_out_proof                        true
% 3.70/1.03  
% 3.70/1.03  ------ Resolution Options
% 3.70/1.03  
% 3.70/1.03  --resolution_flag                       false
% 3.70/1.03  --res_lit_sel                           adaptive
% 3.70/1.03  --res_lit_sel_side                      none
% 3.70/1.03  --res_ordering                          kbo
% 3.70/1.03  --res_to_prop_solver                    active
% 3.70/1.03  --res_prop_simpl_new                    false
% 3.70/1.03  --res_prop_simpl_given                  true
% 3.70/1.03  --res_passive_queue_type                priority_queues
% 3.70/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/1.03  --res_passive_queues_freq               [15;5]
% 3.70/1.03  --res_forward_subs                      full
% 3.70/1.03  --res_backward_subs                     full
% 3.70/1.03  --res_forward_subs_resolution           true
% 3.70/1.03  --res_backward_subs_resolution          true
% 3.70/1.03  --res_orphan_elimination                true
% 3.70/1.03  --res_time_limit                        2.
% 3.70/1.03  --res_out_proof                         true
% 3.70/1.03  
% 3.70/1.03  ------ Superposition Options
% 3.70/1.03  
% 3.70/1.03  --superposition_flag                    true
% 3.70/1.03  --sup_passive_queue_type                priority_queues
% 3.70/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.70/1.03  --demod_completeness_check              fast
% 3.70/1.03  --demod_use_ground                      true
% 3.70/1.03  --sup_to_prop_solver                    passive
% 3.70/1.03  --sup_prop_simpl_new                    true
% 3.70/1.03  --sup_prop_simpl_given                  true
% 3.70/1.03  --sup_fun_splitting                     true
% 3.70/1.03  --sup_smt_interval                      50000
% 3.70/1.03  
% 3.70/1.03  ------ Superposition Simplification Setup
% 3.70/1.03  
% 3.70/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.70/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.70/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.70/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.70/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.70/1.03  --sup_immed_triv                        [TrivRules]
% 3.70/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.03  --sup_immed_bw_main                     []
% 3.70/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.70/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.03  --sup_input_bw                          []
% 3.70/1.03  
% 3.70/1.03  ------ Combination Options
% 3.70/1.03  
% 3.70/1.03  --comb_res_mult                         3
% 3.70/1.03  --comb_sup_mult                         2
% 3.70/1.03  --comb_inst_mult                        10
% 3.70/1.03  
% 3.70/1.03  ------ Debug Options
% 3.70/1.03  
% 3.70/1.03  --dbg_backtrace                         false
% 3.70/1.03  --dbg_dump_prop_clauses                 false
% 3.70/1.03  --dbg_dump_prop_clauses_file            -
% 3.70/1.03  --dbg_out_stat                          false
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  ------ Proving...
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  % SZS status Theorem for theBenchmark.p
% 3.70/1.03  
% 3.70/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.70/1.03  
% 3.70/1.03  fof(f5,axiom,(
% 3.70/1.03    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.03  
% 3.70/1.03  fof(f15,plain,(
% 3.70/1.03    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.70/1.03    inference(rectify,[],[f5])).
% 3.70/1.03  
% 3.70/1.03  fof(f17,plain,(
% 3.70/1.03    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.70/1.03    inference(ennf_transformation,[],[f15])).
% 3.70/1.03  
% 3.70/1.03  fof(f18,plain,(
% 3.70/1.03    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.70/1.03    inference(flattening,[],[f17])).
% 3.70/1.03  
% 3.70/1.03  fof(f31,plain,(
% 3.70/1.03    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.70/1.03    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.70/1.03  
% 3.70/1.03  fof(f32,plain,(
% 3.70/1.03    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.70/1.03    inference(definition_folding,[],[f18,f31])).
% 3.70/1.03  
% 3.70/1.03  fof(f41,plain,(
% 3.70/1.03    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.70/1.03    inference(nnf_transformation,[],[f32])).
% 3.70/1.03  
% 3.70/1.03  fof(f42,plain,(
% 3.70/1.03    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.70/1.03    inference(flattening,[],[f41])).
% 3.70/1.03  
% 3.70/1.03  fof(f43,plain,(
% 3.70/1.03    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.70/1.03    inference(rectify,[],[f42])).
% 3.70/1.03  
% 3.70/1.03  fof(f44,plain,(
% 3.70/1.03    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.70/1.03    introduced(choice_axiom,[])).
% 3.70/1.03  
% 3.70/1.03  fof(f45,plain,(
% 3.70/1.03    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.70/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 3.70/1.03  
% 3.70/1.03  fof(f71,plain,(
% 3.70/1.03    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.70/1.03    inference(cnf_transformation,[],[f45])).
% 3.70/1.03  
% 3.70/1.03  fof(f3,axiom,(
% 3.70/1.03    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.03  
% 3.70/1.03  fof(f62,plain,(
% 3.70/1.03    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.70/1.03    inference(cnf_transformation,[],[f3])).
% 3.70/1.03  
% 3.70/1.03  fof(f2,axiom,(
% 3.70/1.03    ! [X0] : k2_subset_1(X0) = X0),
% 3.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.03  
% 3.70/1.03  fof(f61,plain,(
% 3.70/1.03    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.70/1.03    inference(cnf_transformation,[],[f2])).
% 3.70/1.03  
% 3.70/1.03  fof(f6,axiom,(
% 3.70/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 3.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.03  
% 3.70/1.03  fof(f19,plain,(
% 3.70/1.03    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.70/1.03    inference(ennf_transformation,[],[f6])).
% 3.70/1.03  
% 3.70/1.03  fof(f46,plain,(
% 3.70/1.03    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.70/1.03    inference(nnf_transformation,[],[f19])).
% 3.70/1.03  
% 3.70/1.03  fof(f78,plain,(
% 3.70/1.03    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.70/1.03    inference(cnf_transformation,[],[f46])).
% 3.70/1.03  
% 3.70/1.03  fof(f13,conjecture,(
% 3.70/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 3.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.03  
% 3.70/1.03  fof(f14,negated_conjecture,(
% 3.70/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 3.70/1.03    inference(negated_conjecture,[],[f13])).
% 3.70/1.03  
% 3.70/1.03  fof(f29,plain,(
% 3.70/1.03    ? [X0] : (? [X1] : (? [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2) & (l1_pre_topc(X2) & v2_pre_topc(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.70/1.03    inference(ennf_transformation,[],[f14])).
% 3.70/1.03  
% 3.70/1.03  fof(f30,plain,(
% 3.70/1.03    ? [X0] : (? [X1] : (? [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.70/1.03    inference(flattening,[],[f29])).
% 3.70/1.03  
% 3.70/1.03  fof(f52,plain,(
% 3.70/1.03    ? [X0] : (? [X1] : (? [X2] : ((((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0)) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.70/1.03    inference(nnf_transformation,[],[f30])).
% 3.70/1.03  
% 3.70/1.03  fof(f53,plain,(
% 3.70/1.03    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.70/1.03    inference(flattening,[],[f52])).
% 3.70/1.03  
% 3.70/1.03  fof(f56,plain,(
% 3.70/1.03    ( ! [X0,X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) => ((~m1_pre_topc(sK6,X0) | ~v1_tsep_1(sK6,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(sK6,X0) & v1_tsep_1(sK6,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = sK6 & l1_pre_topc(sK6) & v2_pre_topc(sK6))) )),
% 3.70/1.03    introduced(choice_axiom,[])).
% 3.70/1.03  
% 3.70/1.03  fof(f55,plain,(
% 3.70/1.03    ( ! [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(sK5,X0) | ~v1_tsep_1(sK5,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(sK5,X0) & v1_tsep_1(sK5,X0))) & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(sK5) & v2_pre_topc(sK5))) )),
% 3.70/1.03    introduced(choice_axiom,[])).
% 3.70/1.03  
% 3.70/1.03  fof(f54,plain,(
% 3.70/1.03    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK4) | ~v1_tsep_1(X2,sK4) | ~m1_pre_topc(X1,sK4) | ~v1_tsep_1(X1,sK4)) & ((m1_pre_topc(X2,sK4) & v1_tsep_1(X2,sK4)) | (m1_pre_topc(X1,sK4) & v1_tsep_1(X1,sK4))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 3.70/1.03    introduced(choice_axiom,[])).
% 3.70/1.03  
% 3.70/1.03  fof(f57,plain,(
% 3.70/1.03    (((~m1_pre_topc(sK6,sK4) | ~v1_tsep_1(sK6,sK4) | ~m1_pre_topc(sK5,sK4) | ~v1_tsep_1(sK5,sK4)) & ((m1_pre_topc(sK6,sK4) & v1_tsep_1(sK6,sK4)) | (m1_pre_topc(sK5,sK4) & v1_tsep_1(sK5,sK4))) & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6 & l1_pre_topc(sK6) & v2_pre_topc(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 3.70/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f53,f56,f55,f54])).
% 3.70/1.03  
% 3.70/1.03  fof(f97,plain,(
% 3.70/1.03    g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6),
% 3.70/1.03    inference(cnf_transformation,[],[f57])).
% 3.70/1.03  
% 3.70/1.03  fof(f8,axiom,(
% 3.70/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 3.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.03  
% 3.70/1.03  fof(f21,plain,(
% 3.70/1.03    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.70/1.03    inference(ennf_transformation,[],[f8])).
% 3.70/1.03  
% 3.70/1.03  fof(f22,plain,(
% 3.70/1.03    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.70/1.03    inference(flattening,[],[f21])).
% 3.70/1.03  
% 3.70/1.03  fof(f47,plain,(
% 3.70/1.03    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.70/1.03    inference(nnf_transformation,[],[f22])).
% 3.70/1.03  
% 3.70/1.03  fof(f48,plain,(
% 3.70/1.03    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.70/1.03    inference(flattening,[],[f47])).
% 3.70/1.03  
% 3.70/1.03  fof(f82,plain,(
% 3.70/1.03    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.70/1.03    inference(cnf_transformation,[],[f48])).
% 3.70/1.03  
% 3.70/1.03  fof(f93,plain,(
% 3.70/1.03    v2_pre_topc(sK5)),
% 3.70/1.03    inference(cnf_transformation,[],[f57])).
% 3.70/1.03  
% 3.70/1.03  fof(f94,plain,(
% 3.70/1.03    l1_pre_topc(sK5)),
% 3.70/1.03    inference(cnf_transformation,[],[f57])).
% 3.70/1.03  
% 3.70/1.03  fof(f95,plain,(
% 3.70/1.03    v2_pre_topc(sK6)),
% 3.70/1.03    inference(cnf_transformation,[],[f57])).
% 3.70/1.03  
% 3.70/1.03  fof(f96,plain,(
% 3.70/1.03    l1_pre_topc(sK6)),
% 3.70/1.03    inference(cnf_transformation,[],[f57])).
% 3.70/1.03  
% 3.70/1.03  fof(f12,axiom,(
% 3.70/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.03  
% 3.70/1.03  fof(f28,plain,(
% 3.70/1.03    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.70/1.03    inference(ennf_transformation,[],[f12])).
% 3.70/1.03  
% 3.70/1.03  fof(f90,plain,(
% 3.70/1.03    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.70/1.03    inference(cnf_transformation,[],[f28])).
% 3.70/1.03  
% 3.70/1.03  fof(f80,plain,(
% 3.70/1.03    ( ! [X0,X1] : (v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.70/1.03    inference(cnf_transformation,[],[f48])).
% 3.70/1.03  
% 3.70/1.03  fof(f83,plain,(
% 3.70/1.03    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.70/1.03    inference(cnf_transformation,[],[f48])).
% 3.70/1.03  
% 3.70/1.03  fof(f4,axiom,(
% 3.70/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.03  
% 3.70/1.03  fof(f35,plain,(
% 3.70/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.70/1.03    inference(nnf_transformation,[],[f4])).
% 3.70/1.03  
% 3.70/1.03  fof(f63,plain,(
% 3.70/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.70/1.03    inference(cnf_transformation,[],[f35])).
% 3.70/1.03  
% 3.70/1.03  fof(f81,plain,(
% 3.70/1.03    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.70/1.03    inference(cnf_transformation,[],[f48])).
% 3.70/1.03  
% 3.70/1.03  fof(f1,axiom,(
% 3.70/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.03  
% 3.70/1.03  fof(f33,plain,(
% 3.70/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.70/1.03    inference(nnf_transformation,[],[f1])).
% 3.70/1.03  
% 3.70/1.03  fof(f34,plain,(
% 3.70/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.70/1.03    inference(flattening,[],[f33])).
% 3.70/1.03  
% 3.70/1.03  fof(f60,plain,(
% 3.70/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.70/1.03    inference(cnf_transformation,[],[f34])).
% 3.70/1.03  
% 3.70/1.03  fof(f11,axiom,(
% 3.70/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.03  
% 3.70/1.03  fof(f26,plain,(
% 3.70/1.03    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.70/1.03    inference(ennf_transformation,[],[f11])).
% 3.70/1.03  
% 3.70/1.03  fof(f27,plain,(
% 3.70/1.03    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.70/1.03    inference(flattening,[],[f26])).
% 3.70/1.03  
% 3.70/1.03  fof(f50,plain,(
% 3.70/1.03    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.70/1.03    inference(nnf_transformation,[],[f27])).
% 3.70/1.03  
% 3.70/1.03  fof(f51,plain,(
% 3.70/1.03    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.70/1.03    inference(flattening,[],[f50])).
% 3.70/1.03  
% 3.70/1.03  fof(f88,plain,(
% 3.70/1.03    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.70/1.03    inference(cnf_transformation,[],[f51])).
% 3.70/1.03  
% 3.70/1.03  fof(f108,plain,(
% 3.70/1.03    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.70/1.03    inference(equality_resolution,[],[f88])).
% 3.70/1.03  
% 3.70/1.03  fof(f87,plain,(
% 3.70/1.03    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.70/1.03    inference(cnf_transformation,[],[f51])).
% 3.70/1.03  
% 3.70/1.03  fof(f109,plain,(
% 3.70/1.03    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.70/1.03    inference(equality_resolution,[],[f87])).
% 3.70/1.03  
% 3.70/1.03  fof(f10,axiom,(
% 3.70/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 3.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.03  
% 3.70/1.03  fof(f24,plain,(
% 3.70/1.03    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 3.70/1.03    inference(ennf_transformation,[],[f10])).
% 3.70/1.03  
% 3.70/1.03  fof(f25,plain,(
% 3.70/1.03    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.70/1.03    inference(flattening,[],[f24])).
% 3.70/1.03  
% 3.70/1.03  fof(f49,plain,(
% 3.70/1.03    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.70/1.03    inference(nnf_transformation,[],[f25])).
% 3.70/1.03  
% 3.70/1.03  fof(f85,plain,(
% 3.70/1.03    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.70/1.03    inference(cnf_transformation,[],[f49])).
% 3.70/1.03  
% 3.70/1.03  fof(f106,plain,(
% 3.70/1.03    ( ! [X2,X0] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 3.70/1.03    inference(equality_resolution,[],[f85])).
% 3.70/1.03  
% 3.70/1.03  fof(f101,plain,(
% 3.70/1.03    m1_pre_topc(sK6,sK4) | m1_pre_topc(sK5,sK4)),
% 3.70/1.03    inference(cnf_transformation,[],[f57])).
% 3.70/1.03  
% 3.70/1.03  fof(f9,axiom,(
% 3.70/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.03  
% 3.70/1.03  fof(f16,plain,(
% 3.70/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 3.70/1.03    inference(pure_predicate_removal,[],[f9])).
% 3.70/1.03  
% 3.70/1.03  fof(f23,plain,(
% 3.70/1.03    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.70/1.03    inference(ennf_transformation,[],[f16])).
% 3.70/1.03  
% 3.70/1.03  fof(f84,plain,(
% 3.70/1.03    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.70/1.03    inference(cnf_transformation,[],[f23])).
% 3.70/1.03  
% 3.70/1.03  fof(f102,plain,(
% 3.70/1.03    ~m1_pre_topc(sK6,sK4) | ~v1_tsep_1(sK6,sK4) | ~m1_pre_topc(sK5,sK4) | ~v1_tsep_1(sK5,sK4)),
% 3.70/1.03    inference(cnf_transformation,[],[f57])).
% 3.70/1.03  
% 3.70/1.03  fof(f98,plain,(
% 3.70/1.03    v1_tsep_1(sK6,sK4) | v1_tsep_1(sK5,sK4)),
% 3.70/1.03    inference(cnf_transformation,[],[f57])).
% 3.70/1.03  
% 3.70/1.03  fof(f92,plain,(
% 3.70/1.03    l1_pre_topc(sK4)),
% 3.70/1.03    inference(cnf_transformation,[],[f57])).
% 3.70/1.03  
% 3.70/1.03  fof(f91,plain,(
% 3.70/1.03    v2_pre_topc(sK4)),
% 3.70/1.03    inference(cnf_transformation,[],[f57])).
% 3.70/1.03  
% 3.70/1.03  cnf(c_18,plain,
% 3.70/1.03      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 3.70/1.03      | ~ l1_pre_topc(X0)
% 3.70/1.03      | ~ v2_pre_topc(X0) ),
% 3.70/1.03      inference(cnf_transformation,[],[f71]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_2853,plain,
% 3.70/1.03      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
% 3.70/1.03      | l1_pre_topc(X0) != iProver_top
% 3.70/1.03      | v2_pre_topc(X0) != iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_4,plain,
% 3.70/1.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.70/1.03      inference(cnf_transformation,[],[f62]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_2867,plain,
% 3.70/1.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_3,plain,
% 3.70/1.03      ( k2_subset_1(X0) = X0 ),
% 3.70/1.03      inference(cnf_transformation,[],[f61]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_2870,plain,
% 3.70/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.70/1.03      inference(light_normalisation,[status(thm)],[c_2867,c_3]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_19,plain,
% 3.70/1.03      ( v3_pre_topc(X0,X1)
% 3.70/1.03      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.70/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.70/1.03      | ~ l1_pre_topc(X1) ),
% 3.70/1.03      inference(cnf_transformation,[],[f78]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_2852,plain,
% 3.70/1.03      ( v3_pre_topc(X0,X1) = iProver_top
% 3.70/1.03      | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.70/1.03      | l1_pre_topc(X1) != iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_4640,plain,
% 3.70/1.03      ( v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
% 3.70/1.03      | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) != iProver_top
% 3.70/1.03      | l1_pre_topc(X0) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_2870,c_2852]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_6781,plain,
% 3.70/1.03      ( v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
% 3.70/1.03      | l1_pre_topc(X0) != iProver_top
% 3.70/1.03      | v2_pre_topc(X0) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_2853,c_4640]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_38,negated_conjecture,
% 3.70/1.03      ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6 ),
% 3.70/1.03      inference(cnf_transformation,[],[f97]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_23,plain,
% 3.70/1.03      ( v3_pre_topc(X0,X1)
% 3.70/1.03      | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.70/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 3.70/1.03      | ~ l1_pre_topc(X1)
% 3.70/1.03      | ~ v2_pre_topc(X1) ),
% 3.70/1.03      inference(cnf_transformation,[],[f82]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_2848,plain,
% 3.70/1.03      ( v3_pre_topc(X0,X1) = iProver_top
% 3.70/1.03      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
% 3.70/1.03      | l1_pre_topc(X1) != iProver_top
% 3.70/1.03      | v2_pre_topc(X1) != iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_5391,plain,
% 3.70/1.03      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 3.70/1.03      | v3_pre_topc(X0,sK5) = iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.70/1.03      | l1_pre_topc(sK5) != iProver_top
% 3.70/1.03      | v2_pre_topc(sK5) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_38,c_2848]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_5392,plain,
% 3.70/1.03      ( v3_pre_topc(X0,sK5) = iProver_top
% 3.70/1.03      | v3_pre_topc(X0,sK6) != iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.70/1.03      | l1_pre_topc(sK5) != iProver_top
% 3.70/1.03      | v2_pre_topc(sK5) != iProver_top ),
% 3.70/1.03      inference(light_normalisation,[status(thm)],[c_5391,c_38]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_42,negated_conjecture,
% 3.70/1.03      ( v2_pre_topc(sK5) ),
% 3.70/1.03      inference(cnf_transformation,[],[f93]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_47,plain,
% 3.70/1.03      ( v2_pre_topc(sK5) = iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_41,negated_conjecture,
% 3.70/1.03      ( l1_pre_topc(sK5) ),
% 3.70/1.03      inference(cnf_transformation,[],[f94]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_48,plain,
% 3.70/1.03      ( l1_pre_topc(sK5) = iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_5412,plain,
% 3.70/1.03      ( v3_pre_topc(X0,sK5) = iProver_top
% 3.70/1.03      | v3_pre_topc(X0,sK6) != iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.70/1.03      inference(global_propositional_subsumption,
% 3.70/1.03                [status(thm)],
% 3.70/1.03                [c_5392,c_47,c_48]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_5422,plain,
% 3.70/1.03      ( v3_pre_topc(u1_struct_0(sK6),sK5) = iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_2870,c_5412]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_6790,plain,
% 3.70/1.03      ( v3_pre_topc(u1_struct_0(sK6),sK5) = iProver_top
% 3.70/1.03      | l1_pre_topc(sK6) != iProver_top
% 3.70/1.03      | v2_pre_topc(sK6) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_6781,c_5422]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_40,negated_conjecture,
% 3.70/1.03      ( v2_pre_topc(sK6) ),
% 3.70/1.03      inference(cnf_transformation,[],[f95]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_49,plain,
% 3.70/1.03      ( v2_pre_topc(sK6) = iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_39,negated_conjecture,
% 3.70/1.03      ( l1_pre_topc(sK6) ),
% 3.70/1.03      inference(cnf_transformation,[],[f96]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_50,plain,
% 3.70/1.03      ( l1_pre_topc(sK6) = iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_7030,plain,
% 3.70/1.03      ( v3_pre_topc(u1_struct_0(sK6),sK5) = iProver_top ),
% 3.70/1.03      inference(global_propositional_subsumption,
% 3.70/1.03                [status(thm)],
% 3.70/1.03                [c_6790,c_49,c_50]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_32,plain,
% 3.70/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.70/1.03      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.70/1.03      | ~ l1_pre_topc(X1) ),
% 3.70/1.03      inference(cnf_transformation,[],[f90]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_2843,plain,
% 3.70/1.03      ( m1_pre_topc(X0,X1) != iProver_top
% 3.70/1.03      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.70/1.03      | l1_pre_topc(X1) != iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_25,plain,
% 3.70/1.03      ( ~ v3_pre_topc(X0,X1)
% 3.70/1.03      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.70/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.70/1.03      | ~ l1_pre_topc(X1)
% 3.70/1.03      | ~ v2_pre_topc(X1) ),
% 3.70/1.03      inference(cnf_transformation,[],[f80]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_2846,plain,
% 3.70/1.03      ( v3_pre_topc(X0,X1) != iProver_top
% 3.70/1.03      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.70/1.03      | l1_pre_topc(X1) != iProver_top
% 3.70/1.03      | v2_pre_topc(X1) != iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_4773,plain,
% 3.70/1.03      ( v3_pre_topc(X0,sK5) != iProver_top
% 3.70/1.03      | v3_pre_topc(X0,sK6) = iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.70/1.03      | l1_pre_topc(sK5) != iProver_top
% 3.70/1.03      | v2_pre_topc(sK5) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_38,c_2846]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_4852,plain,
% 3.70/1.03      ( v3_pre_topc(X0,sK5) != iProver_top
% 3.70/1.03      | v3_pre_topc(X0,sK6) = iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 3.70/1.03      inference(global_propositional_subsumption,
% 3.70/1.03                [status(thm)],
% 3.70/1.03                [c_4773,c_47,c_48]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_4861,plain,
% 3.70/1.03      ( m1_pre_topc(X0,sK5) != iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(X0),sK5) != iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(X0),sK6) = iProver_top
% 3.70/1.03      | l1_pre_topc(sK5) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_2843,c_4852]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_5024,plain,
% 3.70/1.03      ( v3_pre_topc(u1_struct_0(X0),sK6) = iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(X0),sK5) != iProver_top
% 3.70/1.03      | m1_pre_topc(X0,sK5) != iProver_top ),
% 3.70/1.03      inference(global_propositional_subsumption,
% 3.70/1.03                [status(thm)],
% 3.70/1.03                [c_4861,c_48]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_5025,plain,
% 3.70/1.03      ( m1_pre_topc(X0,sK5) != iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(X0),sK5) != iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(X0),sK6) = iProver_top ),
% 3.70/1.03      inference(renaming,[status(thm)],[c_5024]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_7035,plain,
% 3.70/1.03      ( m1_pre_topc(sK6,sK5) != iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(sK6),sK6) = iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_7030,c_5025]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_4862,plain,
% 3.70/1.03      ( v3_pre_topc(u1_struct_0(sK5),sK5) != iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(sK5),sK6) = iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_2870,c_4852]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_6789,plain,
% 3.70/1.03      ( v3_pre_topc(u1_struct_0(sK5),sK6) = iProver_top
% 3.70/1.03      | l1_pre_topc(sK5) != iProver_top
% 3.70/1.03      | v2_pre_topc(sK5) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_6781,c_4862]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_6917,plain,
% 3.70/1.03      ( v3_pre_topc(u1_struct_0(sK5),sK6) = iProver_top ),
% 3.70/1.03      inference(global_propositional_subsumption,
% 3.70/1.03                [status(thm)],
% 3.70/1.03                [c_6789,c_47,c_48]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_5421,plain,
% 3.70/1.03      ( m1_pre_topc(X0,sK6) != iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(X0),sK5) = iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(X0),sK6) != iProver_top
% 3.70/1.03      | l1_pre_topc(sK6) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_2843,c_5412]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_5654,plain,
% 3.70/1.03      ( v3_pre_topc(u1_struct_0(X0),sK6) != iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(X0),sK5) = iProver_top
% 3.70/1.03      | m1_pre_topc(X0,sK6) != iProver_top ),
% 3.70/1.03      inference(global_propositional_subsumption,
% 3.70/1.03                [status(thm)],
% 3.70/1.03                [c_5421,c_50]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_5655,plain,
% 3.70/1.03      ( m1_pre_topc(X0,sK6) != iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(X0),sK5) = iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(X0),sK6) != iProver_top ),
% 3.70/1.03      inference(renaming,[status(thm)],[c_5654]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_6922,plain,
% 3.70/1.03      ( m1_pre_topc(sK5,sK6) != iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(sK5),sK5) = iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_6917,c_5655]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_22,plain,
% 3.70/1.03      ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.70/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 3.70/1.03      | ~ l1_pre_topc(X1)
% 3.70/1.03      | ~ v2_pre_topc(X1) ),
% 3.70/1.03      inference(cnf_transformation,[],[f83]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_2849,plain,
% 3.70/1.03      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
% 3.70/1.03      | l1_pre_topc(X1) != iProver_top
% 3.70/1.03      | v2_pre_topc(X1) != iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_5846,plain,
% 3.70/1.03      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.70/1.03      | l1_pre_topc(sK5) != iProver_top
% 3.70/1.03      | v2_pre_topc(sK5) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_38,c_2849]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_5847,plain,
% 3.70/1.03      ( v3_pre_topc(X0,sK6) != iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.70/1.03      | l1_pre_topc(sK5) != iProver_top
% 3.70/1.03      | v2_pre_topc(sK5) != iProver_top ),
% 3.70/1.03      inference(light_normalisation,[status(thm)],[c_5846,c_38]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_5965,plain,
% 3.70/1.03      ( v3_pre_topc(X0,sK6) != iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.70/1.03      inference(global_propositional_subsumption,
% 3.70/1.03                [status(thm)],
% 3.70/1.03                [c_5847,c_47,c_48]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_5975,plain,
% 3.70/1.03      ( v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
% 3.70/1.03      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_2870,c_5965]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_6,plain,
% 3.70/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.70/1.03      inference(cnf_transformation,[],[f63]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_2865,plain,
% 3.70/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.70/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_6206,plain,
% 3.70/1.03      ( v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
% 3.70/1.03      | r1_tarski(u1_struct_0(sK6),u1_struct_0(sK5)) = iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_5975,c_2865]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_24,plain,
% 3.70/1.03      ( ~ v3_pre_topc(X0,X1)
% 3.70/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 3.70/1.03      | ~ l1_pre_topc(X1)
% 3.70/1.03      | ~ v2_pre_topc(X1) ),
% 3.70/1.03      inference(cnf_transformation,[],[f81]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_2847,plain,
% 3.70/1.03      ( v3_pre_topc(X0,X1) != iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) = iProver_top
% 3.70/1.03      | l1_pre_topc(X1) != iProver_top
% 3.70/1.03      | v2_pre_topc(X1) != iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_5183,plain,
% 3.70/1.03      ( v3_pre_topc(X0,sK5) != iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 3.70/1.03      | l1_pre_topc(sK5) != iProver_top
% 3.70/1.03      | v2_pre_topc(sK5) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_38,c_2847]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_5197,plain,
% 3.70/1.03      ( v3_pre_topc(X0,sK5) != iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.70/1.03      inference(global_propositional_subsumption,
% 3.70/1.03                [status(thm)],
% 3.70/1.03                [c_5183,c_47,c_48]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_5207,plain,
% 3.70/1.03      ( v3_pre_topc(u1_struct_0(sK5),sK5) != iProver_top
% 3.70/1.03      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_2870,c_5197]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_5521,plain,
% 3.70/1.03      ( v3_pre_topc(u1_struct_0(sK5),sK5) != iProver_top
% 3.70/1.03      | r1_tarski(u1_struct_0(sK5),u1_struct_0(sK6)) = iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_5207,c_2865]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_0,plain,
% 3.70/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.70/1.03      inference(cnf_transformation,[],[f60]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_2869,plain,
% 3.70/1.03      ( X0 = X1
% 3.70/1.03      | r1_tarski(X0,X1) != iProver_top
% 3.70/1.03      | r1_tarski(X1,X0) != iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_5833,plain,
% 3.70/1.03      ( u1_struct_0(sK6) = u1_struct_0(sK5)
% 3.70/1.03      | v3_pre_topc(u1_struct_0(sK5),sK5) != iProver_top
% 3.70/1.03      | r1_tarski(u1_struct_0(sK6),u1_struct_0(sK5)) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_5521,c_2869]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_7372,plain,
% 3.70/1.03      ( u1_struct_0(sK6) = u1_struct_0(sK5)
% 3.70/1.03      | v3_pre_topc(u1_struct_0(sK5),sK5) != iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_6206,c_5833]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_8578,plain,
% 3.70/1.03      ( u1_struct_0(sK6) = u1_struct_0(sK5)
% 3.70/1.03      | m1_pre_topc(sK5,sK6) != iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_6922,c_7372]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_8575,plain,
% 3.70/1.03      ( u1_struct_0(sK6) = u1_struct_0(sK5)
% 3.70/1.03      | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
% 3.70/1.03      | l1_pre_topc(sK5) != iProver_top
% 3.70/1.03      | v2_pre_topc(sK5) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_6781,c_7372]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_8582,plain,
% 3.70/1.03      ( u1_struct_0(sK6) = u1_struct_0(sK5)
% 3.70/1.03      | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top ),
% 3.70/1.03      inference(global_propositional_subsumption,
% 3.70/1.03                [status(thm)],
% 3.70/1.03                [c_8578,c_47,c_48,c_8575]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_8590,plain,
% 3.70/1.03      ( u1_struct_0(sK6) = u1_struct_0(sK5)
% 3.70/1.03      | m1_pre_topc(sK6,sK5) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_7035,c_8582]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_8587,plain,
% 3.70/1.03      ( u1_struct_0(sK6) = u1_struct_0(sK5)
% 3.70/1.03      | l1_pre_topc(sK6) != iProver_top
% 3.70/1.03      | v2_pre_topc(sK6) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_6781,c_8582]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_8661,plain,
% 3.70/1.03      ( u1_struct_0(sK6) = u1_struct_0(sK5) ),
% 3.70/1.03      inference(global_propositional_subsumption,
% 3.70/1.03                [status(thm)],
% 3.70/1.03                [c_8590,c_49,c_50,c_8587]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_30,plain,
% 3.70/1.03      ( v1_tsep_1(X0,X1)
% 3.70/1.03      | ~ m1_pre_topc(X0,X1)
% 3.70/1.03      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.70/1.03      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.70/1.03      | ~ l1_pre_topc(X1)
% 3.70/1.03      | ~ v2_pre_topc(X1) ),
% 3.70/1.03      inference(cnf_transformation,[],[f108]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_247,plain,
% 3.70/1.03      ( ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.70/1.03      | ~ m1_pre_topc(X0,X1)
% 3.70/1.03      | v1_tsep_1(X0,X1)
% 3.70/1.03      | ~ l1_pre_topc(X1)
% 3.70/1.03      | ~ v2_pre_topc(X1) ),
% 3.70/1.03      inference(global_propositional_subsumption,
% 3.70/1.03                [status(thm)],
% 3.70/1.03                [c_30,c_32]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_248,plain,
% 3.70/1.03      ( v1_tsep_1(X0,X1)
% 3.70/1.03      | ~ m1_pre_topc(X0,X1)
% 3.70/1.03      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.70/1.03      | ~ l1_pre_topc(X1)
% 3.70/1.03      | ~ v2_pre_topc(X1) ),
% 3.70/1.03      inference(renaming,[status(thm)],[c_247]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_2830,plain,
% 3.70/1.03      ( v1_tsep_1(X0,X1) = iProver_top
% 3.70/1.03      | m1_pre_topc(X0,X1) != iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(X0),X1) != iProver_top
% 3.70/1.03      | l1_pre_topc(X1) != iProver_top
% 3.70/1.03      | v2_pre_topc(X1) != iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_248]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_8731,plain,
% 3.70/1.03      ( v1_tsep_1(sK5,X0) = iProver_top
% 3.70/1.03      | m1_pre_topc(sK5,X0) != iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(sK6),X0) != iProver_top
% 3.70/1.03      | l1_pre_topc(X0) != iProver_top
% 3.70/1.03      | v2_pre_topc(X0) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_8661,c_2830]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_8776,plain,
% 3.70/1.03      ( v1_tsep_1(sK5,sK4) = iProver_top
% 3.70/1.03      | m1_pre_topc(sK5,sK4) != iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(sK6),sK4) != iProver_top
% 3.70/1.03      | l1_pre_topc(sK4) != iProver_top
% 3.70/1.03      | v2_pre_topc(sK4) != iProver_top ),
% 3.70/1.03      inference(instantiation,[status(thm)],[c_8731]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_31,plain,
% 3.70/1.03      ( ~ v1_tsep_1(X0,X1)
% 3.70/1.03      | ~ m1_pre_topc(X0,X1)
% 3.70/1.03      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.70/1.03      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.70/1.03      | ~ l1_pre_topc(X1)
% 3.70/1.03      | ~ v2_pre_topc(X1) ),
% 3.70/1.03      inference(cnf_transformation,[],[f109]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_240,plain,
% 3.70/1.03      ( v3_pre_topc(u1_struct_0(X0),X1)
% 3.70/1.03      | ~ m1_pre_topc(X0,X1)
% 3.70/1.03      | ~ v1_tsep_1(X0,X1)
% 3.70/1.03      | ~ l1_pre_topc(X1)
% 3.70/1.03      | ~ v2_pre_topc(X1) ),
% 3.70/1.03      inference(global_propositional_subsumption,
% 3.70/1.03                [status(thm)],
% 3.70/1.03                [c_31,c_32]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_241,plain,
% 3.70/1.03      ( ~ v1_tsep_1(X0,X1)
% 3.70/1.03      | ~ m1_pre_topc(X0,X1)
% 3.70/1.03      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.70/1.03      | ~ l1_pre_topc(X1)
% 3.70/1.03      | ~ v2_pre_topc(X1) ),
% 3.70/1.03      inference(renaming,[status(thm)],[c_240]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_2831,plain,
% 3.70/1.03      ( v1_tsep_1(X0,X1) != iProver_top
% 3.70/1.03      | m1_pre_topc(X0,X1) != iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(X0),X1) = iProver_top
% 3.70/1.03      | l1_pre_topc(X1) != iProver_top
% 3.70/1.03      | v2_pre_topc(X1) != iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_241]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_8730,plain,
% 3.70/1.03      ( v1_tsep_1(sK5,X0) != iProver_top
% 3.70/1.03      | m1_pre_topc(sK5,X0) != iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(sK6),X0) = iProver_top
% 3.70/1.03      | l1_pre_topc(X0) != iProver_top
% 3.70/1.03      | v2_pre_topc(X0) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_8661,c_2831]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_8773,plain,
% 3.70/1.03      ( v1_tsep_1(sK5,sK4) != iProver_top
% 3.70/1.03      | m1_pre_topc(sK5,sK4) != iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(sK6),sK4) = iProver_top
% 3.70/1.03      | l1_pre_topc(sK4) != iProver_top
% 3.70/1.03      | v2_pre_topc(sK4) != iProver_top ),
% 3.70/1.03      inference(instantiation,[status(thm)],[c_8730]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_5134,plain,
% 3.70/1.03      ( ~ v1_tsep_1(sK6,sK4)
% 3.70/1.03      | ~ m1_pre_topc(sK6,sK4)
% 3.70/1.03      | v3_pre_topc(u1_struct_0(sK6),sK4)
% 3.70/1.03      | ~ l1_pre_topc(sK4)
% 3.70/1.03      | ~ v2_pre_topc(sK4) ),
% 3.70/1.03      inference(instantiation,[status(thm)],[c_241]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_5135,plain,
% 3.70/1.03      ( v1_tsep_1(sK6,sK4) != iProver_top
% 3.70/1.03      | m1_pre_topc(sK6,sK4) != iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(sK6),sK4) = iProver_top
% 3.70/1.03      | l1_pre_topc(sK4) != iProver_top
% 3.70/1.03      | v2_pre_topc(sK4) != iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_5134]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_28,plain,
% 3.70/1.03      ( m1_pre_topc(X0,X1)
% 3.70/1.03      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.70/1.03      | ~ l1_pre_topc(X1)
% 3.70/1.03      | ~ l1_pre_topc(X0)
% 3.70/1.03      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.70/1.03      | ~ v2_pre_topc(X0)
% 3.70/1.03      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.70/1.03      inference(cnf_transformation,[],[f106]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_2844,plain,
% 3.70/1.03      ( m1_pre_topc(X0,X1) = iProver_top
% 3.70/1.03      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 3.70/1.03      | l1_pre_topc(X1) != iProver_top
% 3.70/1.03      | l1_pre_topc(X0) != iProver_top
% 3.70/1.03      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 3.70/1.03      | v2_pre_topc(X0) != iProver_top
% 3.70/1.03      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_4535,plain,
% 3.70/1.03      ( m1_pre_topc(sK5,X0) = iProver_top
% 3.70/1.03      | m1_pre_topc(sK6,X0) != iProver_top
% 3.70/1.03      | l1_pre_topc(X0) != iProver_top
% 3.70/1.03      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 3.70/1.03      | l1_pre_topc(sK5) != iProver_top
% 3.70/1.03      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 3.70/1.03      | v2_pre_topc(sK5) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_38,c_2844]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_4536,plain,
% 3.70/1.03      ( m1_pre_topc(sK5,X0) = iProver_top
% 3.70/1.03      | m1_pre_topc(sK6,X0) != iProver_top
% 3.70/1.03      | l1_pre_topc(X0) != iProver_top
% 3.70/1.03      | l1_pre_topc(sK5) != iProver_top
% 3.70/1.03      | l1_pre_topc(sK6) != iProver_top
% 3.70/1.03      | v2_pre_topc(sK5) != iProver_top
% 3.70/1.03      | v2_pre_topc(sK6) != iProver_top ),
% 3.70/1.03      inference(light_normalisation,[status(thm)],[c_4535,c_38]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_4538,plain,
% 3.70/1.03      ( m1_pre_topc(sK5,sK4) = iProver_top
% 3.70/1.03      | m1_pre_topc(sK6,sK4) != iProver_top
% 3.70/1.03      | l1_pre_topc(sK5) != iProver_top
% 3.70/1.03      | l1_pre_topc(sK4) != iProver_top
% 3.70/1.03      | l1_pre_topc(sK6) != iProver_top
% 3.70/1.03      | v2_pre_topc(sK5) != iProver_top
% 3.70/1.03      | v2_pre_topc(sK6) != iProver_top ),
% 3.70/1.03      inference(instantiation,[status(thm)],[c_4536]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_34,negated_conjecture,
% 3.70/1.03      ( m1_pre_topc(sK5,sK4) | m1_pre_topc(sK6,sK4) ),
% 3.70/1.03      inference(cnf_transformation,[],[f101]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_2841,plain,
% 3.70/1.03      ( m1_pre_topc(sK5,sK4) = iProver_top
% 3.70/1.03      | m1_pre_topc(sK6,sK4) = iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_26,plain,
% 3.70/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.70/1.03      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.70/1.03      | ~ l1_pre_topc(X1) ),
% 3.70/1.03      inference(cnf_transformation,[],[f84]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_2845,plain,
% 3.70/1.03      ( m1_pre_topc(X0,X1) != iProver_top
% 3.70/1.03      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 3.70/1.03      | l1_pre_topc(X1) != iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_4143,plain,
% 3.70/1.03      ( m1_pre_topc(sK5,X0) != iProver_top
% 3.70/1.03      | m1_pre_topc(sK6,X0) = iProver_top
% 3.70/1.03      | l1_pre_topc(X0) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_38,c_2845]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_4152,plain,
% 3.70/1.03      ( m1_pre_topc(sK6,sK4) = iProver_top
% 3.70/1.03      | l1_pre_topc(sK4) != iProver_top ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_2841,c_4143]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_2924,plain,
% 3.70/1.03      ( v1_tsep_1(sK6,sK4)
% 3.70/1.03      | ~ m1_pre_topc(sK6,sK4)
% 3.70/1.03      | ~ v3_pre_topc(u1_struct_0(sK6),sK4)
% 3.70/1.03      | ~ l1_pre_topc(sK4)
% 3.70/1.03      | ~ v2_pre_topc(sK4) ),
% 3.70/1.03      inference(instantiation,[status(thm)],[c_248]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_2925,plain,
% 3.70/1.03      ( v1_tsep_1(sK6,sK4) = iProver_top
% 3.70/1.03      | m1_pre_topc(sK6,sK4) != iProver_top
% 3.70/1.03      | v3_pre_topc(u1_struct_0(sK6),sK4) != iProver_top
% 3.70/1.03      | l1_pre_topc(sK4) != iProver_top
% 3.70/1.03      | v2_pre_topc(sK4) != iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_2924]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_33,negated_conjecture,
% 3.70/1.03      ( ~ v1_tsep_1(sK5,sK4)
% 3.70/1.03      | ~ v1_tsep_1(sK6,sK4)
% 3.70/1.03      | ~ m1_pre_topc(sK5,sK4)
% 3.70/1.03      | ~ m1_pre_topc(sK6,sK4) ),
% 3.70/1.03      inference(cnf_transformation,[],[f102]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_55,plain,
% 3.70/1.03      ( v1_tsep_1(sK5,sK4) != iProver_top
% 3.70/1.03      | v1_tsep_1(sK6,sK4) != iProver_top
% 3.70/1.03      | m1_pre_topc(sK5,sK4) != iProver_top
% 3.70/1.03      | m1_pre_topc(sK6,sK4) != iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_37,negated_conjecture,
% 3.70/1.03      ( v1_tsep_1(sK5,sK4) | v1_tsep_1(sK6,sK4) ),
% 3.70/1.03      inference(cnf_transformation,[],[f98]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_51,plain,
% 3.70/1.03      ( v1_tsep_1(sK5,sK4) = iProver_top
% 3.70/1.03      | v1_tsep_1(sK6,sK4) = iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_43,negated_conjecture,
% 3.70/1.03      ( l1_pre_topc(sK4) ),
% 3.70/1.03      inference(cnf_transformation,[],[f92]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_46,plain,
% 3.70/1.03      ( l1_pre_topc(sK4) = iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_44,negated_conjecture,
% 3.70/1.03      ( v2_pre_topc(sK4) ),
% 3.70/1.03      inference(cnf_transformation,[],[f91]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_45,plain,
% 3.70/1.03      ( v2_pre_topc(sK4) = iProver_top ),
% 3.70/1.03      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(contradiction,plain,
% 3.70/1.03      ( $false ),
% 3.70/1.03      inference(minisat,
% 3.70/1.03                [status(thm)],
% 3.70/1.03                [c_8776,c_8773,c_5135,c_4538,c_4152,c_2925,c_55,c_51,
% 3.70/1.03                 c_50,c_49,c_48,c_47,c_46,c_45]) ).
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.70/1.03  
% 3.70/1.03  ------                               Statistics
% 3.70/1.03  
% 3.70/1.03  ------ General
% 3.70/1.03  
% 3.70/1.03  abstr_ref_over_cycles:                  0
% 3.70/1.03  abstr_ref_under_cycles:                 0
% 3.70/1.03  gc_basic_clause_elim:                   0
% 3.70/1.03  forced_gc_time:                         0
% 3.70/1.03  parsing_time:                           0.014
% 3.70/1.03  unif_index_cands_time:                  0.
% 3.70/1.03  unif_index_add_time:                    0.
% 3.70/1.03  orderings_time:                         0.
% 3.70/1.03  out_proof_time:                         0.018
% 3.70/1.03  total_time:                             0.328
% 3.70/1.03  num_of_symbols:                         53
% 3.70/1.03  num_of_terms:                           5408
% 3.70/1.03  
% 3.70/1.03  ------ Preprocessing
% 3.70/1.03  
% 3.70/1.03  num_of_splits:                          0
% 3.70/1.03  num_of_split_atoms:                     0
% 3.70/1.03  num_of_reused_defs:                     0
% 3.70/1.03  num_eq_ax_congr_red:                    15
% 3.70/1.03  num_of_sem_filtered_clauses:            1
% 3.70/1.03  num_of_subtypes:                        0
% 3.70/1.03  monotx_restored_types:                  0
% 3.70/1.03  sat_num_of_epr_types:                   0
% 3.70/1.03  sat_num_of_non_cyclic_types:            0
% 3.70/1.03  sat_guarded_non_collapsed_types:        0
% 3.70/1.03  num_pure_diseq_elim:                    0
% 3.70/1.03  simp_replaced_by:                       0
% 3.70/1.03  res_preprocessed:                       201
% 3.70/1.03  prep_upred:                             0
% 3.70/1.03  prep_unflattend:                        12
% 3.70/1.03  smt_new_axioms:                         0
% 3.70/1.03  pred_elim_cands:                        9
% 3.70/1.03  pred_elim:                              0
% 3.70/1.03  pred_elim_cl:                           0
% 3.70/1.03  pred_elim_cycles:                       2
% 3.70/1.03  merged_defs:                            8
% 3.70/1.03  merged_defs_ncl:                        0
% 3.70/1.03  bin_hyper_res:                          8
% 3.70/1.03  prep_cycles:                            4
% 3.70/1.03  pred_elim_time:                         0.022
% 3.70/1.03  splitting_time:                         0.
% 3.70/1.03  sem_filter_time:                        0.
% 3.70/1.03  monotx_time:                            0.
% 3.70/1.03  subtype_inf_time:                       0.
% 3.70/1.03  
% 3.70/1.03  ------ Problem properties
% 3.70/1.03  
% 3.70/1.03  clauses:                                42
% 3.70/1.03  conjectures:                            12
% 3.70/1.03  epr:                                    15
% 3.70/1.03  horn:                                   32
% 3.70/1.03  ground:                                 12
% 3.70/1.03  unary:                                  10
% 3.70/1.03  binary:                                 11
% 3.70/1.03  lits:                                   125
% 3.70/1.03  lits_eq:                                3
% 3.70/1.03  fd_pure:                                0
% 3.70/1.03  fd_pseudo:                              0
% 3.70/1.03  fd_cond:                                0
% 3.70/1.03  fd_pseudo_cond:                         1
% 3.70/1.03  ac_symbols:                             0
% 3.70/1.03  
% 3.70/1.03  ------ Propositional Solver
% 3.70/1.03  
% 3.70/1.03  prop_solver_calls:                      34
% 3.70/1.03  prop_fast_solver_calls:                 1934
% 3.70/1.03  smt_solver_calls:                       0
% 3.70/1.03  smt_fast_solver_calls:                  0
% 3.70/1.03  prop_num_of_clauses:                    3398
% 3.70/1.03  prop_preprocess_simplified:             9142
% 3.70/1.03  prop_fo_subsumed:                       66
% 3.70/1.03  prop_solver_time:                       0.
% 3.70/1.03  smt_solver_time:                        0.
% 3.70/1.03  smt_fast_solver_time:                   0.
% 3.70/1.03  prop_fast_solver_time:                  0.
% 3.70/1.03  prop_unsat_core_time:                   0.
% 3.70/1.03  
% 3.70/1.03  ------ QBF
% 3.70/1.03  
% 3.70/1.03  qbf_q_res:                              0
% 3.70/1.03  qbf_num_tautologies:                    0
% 3.70/1.03  qbf_prep_cycles:                        0
% 3.70/1.03  
% 3.70/1.03  ------ BMC1
% 3.70/1.03  
% 3.70/1.03  bmc1_current_bound:                     -1
% 3.70/1.03  bmc1_last_solved_bound:                 -1
% 3.70/1.03  bmc1_unsat_core_size:                   -1
% 3.70/1.03  bmc1_unsat_core_parents_size:           -1
% 3.70/1.03  bmc1_merge_next_fun:                    0
% 3.70/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.70/1.03  
% 3.70/1.03  ------ Instantiation
% 3.70/1.03  
% 3.70/1.03  inst_num_of_clauses:                    936
% 3.70/1.03  inst_num_in_passive:                    344
% 3.70/1.03  inst_num_in_active:                     520
% 3.70/1.03  inst_num_in_unprocessed:                72
% 3.70/1.03  inst_num_of_loops:                      601
% 3.70/1.03  inst_num_of_learning_restarts:          0
% 3.70/1.03  inst_num_moves_active_passive:          73
% 3.70/1.03  inst_lit_activity:                      0
% 3.70/1.03  inst_lit_activity_moves:                0
% 3.70/1.03  inst_num_tautologies:                   0
% 3.70/1.03  inst_num_prop_implied:                  0
% 3.70/1.03  inst_num_existing_simplified:           0
% 3.70/1.03  inst_num_eq_res_simplified:             0
% 3.70/1.03  inst_num_child_elim:                    0
% 3.70/1.03  inst_num_of_dismatching_blockings:      198
% 3.70/1.03  inst_num_of_non_proper_insts:           1346
% 3.70/1.03  inst_num_of_duplicates:                 0
% 3.70/1.03  inst_inst_num_from_inst_to_res:         0
% 3.70/1.03  inst_dismatching_checking_time:         0.
% 3.70/1.03  
% 3.70/1.03  ------ Resolution
% 3.70/1.03  
% 3.70/1.03  res_num_of_clauses:                     0
% 3.70/1.03  res_num_in_passive:                     0
% 3.70/1.03  res_num_in_active:                      0
% 3.70/1.03  res_num_of_loops:                       205
% 3.70/1.03  res_forward_subset_subsumed:            247
% 3.70/1.03  res_backward_subset_subsumed:           0
% 3.70/1.03  res_forward_subsumed:                   0
% 3.70/1.03  res_backward_subsumed:                  0
% 3.70/1.03  res_forward_subsumption_resolution:     0
% 3.70/1.03  res_backward_subsumption_resolution:    0
% 3.70/1.03  res_clause_to_clause_subsumption:       575
% 3.70/1.03  res_orphan_elimination:                 0
% 3.70/1.03  res_tautology_del:                      124
% 3.70/1.03  res_num_eq_res_simplified:              0
% 3.70/1.03  res_num_sel_changes:                    0
% 3.70/1.03  res_moves_from_active_to_pass:          0
% 3.70/1.03  
% 3.70/1.03  ------ Superposition
% 3.70/1.03  
% 3.70/1.03  sup_time_total:                         0.
% 3.70/1.03  sup_time_generating:                    0.
% 3.70/1.03  sup_time_sim_full:                      0.
% 3.70/1.03  sup_time_sim_immed:                     0.
% 3.70/1.03  
% 3.70/1.03  sup_num_of_clauses:                     160
% 3.70/1.03  sup_num_in_active:                      87
% 3.70/1.03  sup_num_in_passive:                     73
% 3.70/1.03  sup_num_of_loops:                       120
% 3.70/1.03  sup_fw_superposition:                   153
% 3.70/1.03  sup_bw_superposition:                   174
% 3.70/1.03  sup_immediate_simplified:               120
% 3.70/1.03  sup_given_eliminated:                   0
% 3.70/1.03  comparisons_done:                       0
% 3.70/1.03  comparisons_avoided:                    0
% 3.70/1.03  
% 3.70/1.03  ------ Simplifications
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  sim_fw_subset_subsumed:                 60
% 3.70/1.03  sim_bw_subset_subsumed:                 13
% 3.70/1.03  sim_fw_subsumed:                        37
% 3.70/1.03  sim_bw_subsumed:                        9
% 3.70/1.03  sim_fw_subsumption_res:                 0
% 3.70/1.03  sim_bw_subsumption_res:                 0
% 3.70/1.03  sim_tautology_del:                      41
% 3.70/1.03  sim_eq_tautology_del:                   5
% 3.70/1.03  sim_eq_res_simp:                        0
% 3.70/1.03  sim_fw_demodulated:                     2
% 3.70/1.03  sim_bw_demodulated:                     21
% 3.70/1.03  sim_light_normalised:                   27
% 3.70/1.03  sim_joinable_taut:                      0
% 3.70/1.03  sim_joinable_simp:                      0
% 3.70/1.03  sim_ac_normalised:                      0
% 3.70/1.03  sim_smt_subsumption:                    0
% 3.70/1.03  
%------------------------------------------------------------------------------
