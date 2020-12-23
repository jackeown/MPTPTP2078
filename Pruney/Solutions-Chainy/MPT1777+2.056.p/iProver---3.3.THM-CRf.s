%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:36 EST 2020

% Result     : Theorem 11.97s
% Output     : CNFRefutation 11.97s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 638 expanded)
%              Number of clauses        :  119 ( 154 expanded)
%              Number of leaves         :   23 ( 270 expanded)
%              Depth                    :   24
%              Number of atoms          : 1233 (8838 expanded)
%              Number of equality atoms :  232 (1266 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
               => ( m1_pre_topc(X1,X2)
                  & v1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
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

fof(f17,plain,(
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
    inference(rectify,[],[f2])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f41,plain,(
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

fof(f42,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f22,f41])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f50,f51])).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f92,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_tmap_1(X3,X1,X4,X5)
          & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X3,X1,X4,X5)
        & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK10)
        & sK10 = X5
        & m1_subset_1(sK10,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(X3,X1,X4,X5)
              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ? [X6] :
            ( ~ r1_tmap_1(X3,X1,X4,sK9)
            & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            & sK9 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK9,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(X3,X1,X4,X5)
                  & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(X2)) )
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(X3,X1,sK8,X5)
                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK8),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK8,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X3,X1,X4,X5)
                      & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(X2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(sK7,X1,X4,X5)
                    & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK7,X2,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK7)) )
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK7
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK7,X0)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X3,X1,X4,X5)
                          & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(X3,X1,X4,X5)
                        & r1_tmap_1(sK6,X1,k3_tmap_1(X0,X1,X3,sK6,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK6)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X3,sK5,X4,X5)
                            & r1_tmap_1(X2,sK5,k3_tmap_1(X0,sK5,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK5)
        & v2_pre_topc(sK5)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X3,X1,X4,X5)
                                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK4,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK4)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK4)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ~ r1_tmap_1(sK7,sK5,sK8,sK9)
    & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)
    & sK9 = sK10
    & m1_subset_1(sK10,u1_struct_0(sK6))
    & m1_subset_1(sK9,u1_struct_0(sK7))
    & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
    & v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))
    & v1_funct_1(sK8)
    & m1_pre_topc(sK7,sK4)
    & ~ v2_struct_0(sK7)
    & m1_pre_topc(sK6,sK4)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f40,f64,f63,f62,f61,f60,f59,f58])).

fof(f110,plain,(
    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
    inference(cnf_transformation,[],[f65])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f81,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f99,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f104,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f114,plain,(
    r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
    inference(cnf_transformation,[],[f65])).

fof(f113,plain,(
    sK9 = sK10 ),
    inference(cnf_transformation,[],[f65])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X3,X1,X4,X5)
                                  | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) ) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f96,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X5)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f119,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f108,plain,(
    v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f65])).

fof(f107,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f65])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f100,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f101,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f102,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f105,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f65])).

fof(f109,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f65])).

fof(f97,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f98,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f103,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f106,plain,(
    m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f111,plain,(
    m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f65])).

fof(f115,plain,(
    ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
    inference(cnf_transformation,[],[f65])).

fof(f112,plain,(
    m1_subset_1(sK10,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f65])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_24,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v1_tsep_1(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2558,plain,
    ( ~ v1_tsep_1(X0_59,X1_59)
    | v1_tsep_1(X0_59,X2_59)
    | ~ r1_tarski(u1_struct_0(X0_59),u1_struct_0(X2_59))
    | ~ m1_pre_topc(X0_59,X1_59)
    | ~ m1_pre_topc(X2_59,X1_59)
    | v2_struct_0(X1_59)
    | v2_struct_0(X2_59)
    | ~ l1_pre_topc(X1_59)
    | ~ v2_pre_topc(X1_59) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_3492,plain,
    ( ~ v1_tsep_1(X0_59,X1_59)
    | v1_tsep_1(X0_59,sK7)
    | ~ r1_tarski(u1_struct_0(X0_59),u1_struct_0(sK7))
    | ~ m1_pre_topc(X0_59,X1_59)
    | ~ m1_pre_topc(sK7,X1_59)
    | v2_struct_0(X1_59)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(X1_59)
    | ~ v2_pre_topc(X1_59) ),
    inference(instantiation,[status(thm)],[c_2558])).

cnf(c_7638,plain,
    ( ~ v1_tsep_1(X0_59,sK6)
    | v1_tsep_1(X0_59,sK7)
    | ~ r1_tarski(u1_struct_0(X0_59),u1_struct_0(sK7))
    | ~ m1_pre_topc(X0_59,sK6)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_3492])).

cnf(c_30209,plain,
    ( ~ v1_tsep_1(sK6,sK6)
    | v1_tsep_1(sK6,sK7)
    | ~ r1_tarski(u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ m1_pre_topc(sK6,sK6)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_7638])).

cnf(c_12,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2563,plain,
    ( r2_hidden(u1_struct_0(X0_59),u1_pre_topc(X0_59))
    | ~ l1_pre_topc(X0_59)
    | ~ v2_pre_topc(X0_59) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_12415,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_2563])).

cnf(c_27,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2555,plain,
    ( r1_tarski(u1_struct_0(X0_59),u1_struct_0(X1_59))
    | ~ m1_pre_topc(X0_59,X1_59)
    | ~ l1_pre_topc(X1_59) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_3947,plain,
    ( r1_tarski(u1_struct_0(X0_59),u1_struct_0(sK7))
    | ~ m1_pre_topc(X0_59,sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_2555])).

cnf(c_8168,plain,
    ( r1_tarski(u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ m1_pre_topc(sK6,sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_3947])).

cnf(c_13,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_21,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_25,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_267,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_25])).

cnf(c_268,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_267])).

cnf(c_515,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r2_hidden(X2,u1_pre_topc(X3))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | X1 != X3
    | u1_struct_0(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_268])).

cnf(c_516,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_520,plain,
    ( v1_tsep_1(X0,X1)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_516,c_25])).

cnf(c_2535,plain,
    ( v1_tsep_1(X0_59,X1_59)
    | ~ r2_hidden(u1_struct_0(X0_59),u1_pre_topc(X1_59))
    | ~ m1_pre_topc(X0_59,X1_59)
    | ~ l1_pre_topc(X1_59)
    | ~ v2_pre_topc(X1_59) ),
    inference(subtyping,[status(esa)],[c_520])).

cnf(c_4637,plain,
    ( v1_tsep_1(sK6,X0_59)
    | ~ r2_hidden(u1_struct_0(sK6),u1_pre_topc(X0_59))
    | ~ m1_pre_topc(sK6,X0_59)
    | ~ l1_pre_topc(X0_59)
    | ~ v2_pre_topc(X0_59) ),
    inference(instantiation,[status(thm)],[c_2535])).

cnf(c_6889,plain,
    ( v1_tsep_1(sK6,sK6)
    | ~ r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
    | ~ m1_pre_topc(sK6,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_4637])).

cnf(c_26,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2556,plain,
    ( m1_pre_topc(X0_59,X0_59)
    | ~ l1_pre_topc(X0_59) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_3314,plain,
    ( m1_pre_topc(X0_59,X0_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2556])).

cnf(c_36,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2548,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_275,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_15])).

cnf(c_276,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_275])).

cnf(c_2536,plain,
    ( ~ m1_pre_topc(X0_59,X1_59)
    | m1_pre_topc(X0_59,g1_pre_topc(u1_struct_0(X1_59),u1_pre_topc(X1_59)))
    | ~ l1_pre_topc(X1_59) ),
    inference(subtyping,[status(esa)],[c_276])).

cnf(c_3332,plain,
    ( m1_pre_topc(X0_59,X1_59) != iProver_top
    | m1_pre_topc(X0_59,g1_pre_topc(u1_struct_0(X1_59),u1_pre_topc(X1_59))) = iProver_top
    | l1_pre_topc(X1_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2536])).

cnf(c_6642,plain,
    ( m1_pre_topc(X0_59,sK6) != iProver_top
    | m1_pre_topc(X0_59,sK7) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2548,c_3332])).

cnf(c_47,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_52,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_42,negated_conjecture,
    ( m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_57,plain,
    ( m1_pre_topc(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_2562,plain,
    ( ~ m1_pre_topc(X0_59,X1_59)
    | ~ l1_pre_topc(X1_59)
    | l1_pre_topc(X0_59) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_3745,plain,
    ( ~ m1_pre_topc(sK6,X0_59)
    | ~ l1_pre_topc(X0_59)
    | l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_2562])).

cnf(c_4491,plain,
    ( ~ m1_pre_topc(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_3745])).

cnf(c_4492,plain,
    ( m1_pre_topc(sK6,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4491])).

cnf(c_6659,plain,
    ( m1_pre_topc(X0_59,sK7) = iProver_top
    | m1_pre_topc(X0_59,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6642,c_52,c_57,c_4492])).

cnf(c_6660,plain,
    ( m1_pre_topc(X0_59,sK6) != iProver_top
    | m1_pre_topc(X0_59,sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_6659])).

cnf(c_6665,plain,
    ( m1_pre_topc(sK6,sK7) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3314,c_6660])).

cnf(c_6669,plain,
    ( m1_pre_topc(sK6,sK7)
    | ~ l1_pre_topc(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6665])).

cnf(c_6203,plain,
    ( m1_pre_topc(sK6,sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_2556])).

cnf(c_16,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2561,plain,
    ( m1_pre_topc(X0_59,X1_59)
    | ~ m1_pre_topc(X0_59,g1_pre_topc(u1_struct_0(X1_59),u1_pre_topc(X1_59)))
    | ~ l1_pre_topc(X1_59) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3309,plain,
    ( m1_pre_topc(X0_59,X1_59) = iProver_top
    | m1_pre_topc(X0_59,g1_pre_topc(u1_struct_0(X1_59),u1_pre_topc(X1_59))) != iProver_top
    | l1_pre_topc(X1_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2561])).

cnf(c_5189,plain,
    ( m1_pre_topc(X0_59,sK6) = iProver_top
    | m1_pre_topc(X0_59,sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2548,c_3309])).

cnf(c_5197,plain,
    ( m1_pre_topc(X0_59,sK7) != iProver_top
    | m1_pre_topc(X0_59,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5189,c_52,c_57,c_4492])).

cnf(c_5198,plain,
    ( m1_pre_topc(X0_59,sK6) = iProver_top
    | m1_pre_topc(X0_59,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_5197])).

cnf(c_5203,plain,
    ( m1_pre_topc(sK7,sK6) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3314,c_5198])).

cnf(c_5204,plain,
    ( m1_pre_topc(sK7,sK6)
    | ~ l1_pre_topc(sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5203])).

cnf(c_3869,plain,
    ( ~ m1_pre_topc(sK7,X0_59)
    | ~ l1_pre_topc(X0_59)
    | l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_2562])).

cnf(c_4645,plain,
    ( ~ m1_pre_topc(sK7,sK4)
    | ~ l1_pre_topc(sK4)
    | l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_3869])).

cnf(c_32,negated_conjecture,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2552,negated_conjecture,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_3318,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2552])).

cnf(c_33,negated_conjecture,
    ( sK9 = sK10 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2551,negated_conjecture,
    ( sK9 = sK10 ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_3338,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3318,c_2551])).

cnf(c_29,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_650,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_38])).

cnf(c_651,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v1_funct_1(sK8)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_650])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_655,plain,
    ( ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ v1_tsep_1(X0,X3)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_651,c_39])).

cnf(c_656,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(renaming,[status(thm)],[c_655])).

cnf(c_28,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_699,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_656,c_28])).

cnf(c_2532,plain,
    ( ~ r1_tmap_1(X0_59,X1_59,k3_tmap_1(X2_59,X1_59,X3_59,X0_59,sK8),X0_60)
    | r1_tmap_1(X3_59,X1_59,sK8,X0_60)
    | ~ v1_tsep_1(X0_59,X3_59)
    | ~ m1_subset_1(X0_60,u1_struct_0(X0_59))
    | ~ m1_subset_1(X0_60,u1_struct_0(X3_59))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_59),u1_struct_0(X1_59))))
    | ~ m1_pre_topc(X0_59,X3_59)
    | ~ m1_pre_topc(X3_59,X2_59)
    | v2_struct_0(X1_59)
    | v2_struct_0(X2_59)
    | v2_struct_0(X0_59)
    | v2_struct_0(X3_59)
    | ~ l1_pre_topc(X1_59)
    | ~ l1_pre_topc(X2_59)
    | ~ v2_pre_topc(X1_59)
    | ~ v2_pre_topc(X2_59)
    | u1_struct_0(X1_59) != u1_struct_0(sK5)
    | u1_struct_0(X3_59) != u1_struct_0(sK7) ),
    inference(subtyping,[status(esa)],[c_699])).

cnf(c_3336,plain,
    ( u1_struct_0(X0_59) != u1_struct_0(sK5)
    | u1_struct_0(X1_59) != u1_struct_0(sK7)
    | r1_tmap_1(X2_59,X0_59,k3_tmap_1(X3_59,X0_59,X1_59,X2_59,sK8),X0_60) != iProver_top
    | r1_tmap_1(X1_59,X0_59,sK8,X0_60) = iProver_top
    | v1_tsep_1(X2_59,X1_59) != iProver_top
    | m1_subset_1(X0_60,u1_struct_0(X2_59)) != iProver_top
    | m1_subset_1(X0_60,u1_struct_0(X1_59)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_59),u1_struct_0(X0_59)))) != iProver_top
    | m1_pre_topc(X2_59,X1_59) != iProver_top
    | m1_pre_topc(X1_59,X3_59) != iProver_top
    | v2_struct_0(X2_59) = iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v2_struct_0(X3_59) = iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | l1_pre_topc(X0_59) != iProver_top
    | l1_pre_topc(X3_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_pre_topc(X3_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2532])).

cnf(c_4439,plain,
    ( u1_struct_0(X0_59) != u1_struct_0(sK7)
    | r1_tmap_1(X1_59,sK5,k3_tmap_1(X2_59,sK5,X0_59,X1_59,sK8),X0_60) != iProver_top
    | r1_tmap_1(X0_59,sK5,sK8,X0_60) = iProver_top
    | v1_tsep_1(X1_59,X0_59) != iProver_top
    | m1_subset_1(X0_60,u1_struct_0(X0_59)) != iProver_top
    | m1_subset_1(X0_60,u1_struct_0(X1_59)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(sK5)))) != iProver_top
    | m1_pre_topc(X0_59,X2_59) != iProver_top
    | m1_pre_topc(X1_59,X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v2_struct_0(X2_59) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(X2_59) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(X2_59) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3336])).

cnf(c_46,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_53,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_54,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_55,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_4516,plain,
    ( v2_pre_topc(X2_59) != iProver_top
    | v2_struct_0(X2_59) = iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | m1_pre_topc(X1_59,X0_59) != iProver_top
    | m1_pre_topc(X0_59,X2_59) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(sK5)))) != iProver_top
    | m1_subset_1(X0_60,u1_struct_0(X1_59)) != iProver_top
    | m1_subset_1(X0_60,u1_struct_0(X0_59)) != iProver_top
    | v1_tsep_1(X1_59,X0_59) != iProver_top
    | r1_tmap_1(X0_59,sK5,sK8,X0_60) = iProver_top
    | r1_tmap_1(X1_59,sK5,k3_tmap_1(X2_59,sK5,X0_59,X1_59,sK8),X0_60) != iProver_top
    | u1_struct_0(X0_59) != u1_struct_0(sK7)
    | l1_pre_topc(X2_59) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4439,c_53,c_54,c_55])).

cnf(c_4517,plain,
    ( u1_struct_0(X0_59) != u1_struct_0(sK7)
    | r1_tmap_1(X1_59,sK5,k3_tmap_1(X2_59,sK5,X0_59,X1_59,sK8),X0_60) != iProver_top
    | r1_tmap_1(X0_59,sK5,sK8,X0_60) = iProver_top
    | v1_tsep_1(X1_59,X0_59) != iProver_top
    | m1_subset_1(X0_60,u1_struct_0(X0_59)) != iProver_top
    | m1_subset_1(X0_60,u1_struct_0(X1_59)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(sK5)))) != iProver_top
    | m1_pre_topc(X0_59,X2_59) != iProver_top
    | m1_pre_topc(X1_59,X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v2_struct_0(X2_59) = iProver_top
    | l1_pre_topc(X2_59) != iProver_top
    | v2_pre_topc(X2_59) != iProver_top ),
    inference(renaming,[status(thm)],[c_4516])).

cnf(c_4520,plain,
    ( r1_tmap_1(X0_59,sK5,k3_tmap_1(X1_59,sK5,sK7,X0_59,sK8),X0_60) != iProver_top
    | r1_tmap_1(sK7,sK5,sK8,X0_60) = iProver_top
    | v1_tsep_1(X0_59,sK7) != iProver_top
    | m1_subset_1(X0_60,u1_struct_0(X0_59)) != iProver_top
    | m1_subset_1(X0_60,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
    | m1_pre_topc(X0_59,sK7) != iProver_top
    | m1_pre_topc(sK7,X1_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | l1_pre_topc(X1_59) != iProver_top
    | v2_pre_topc(X1_59) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4517])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_58,plain,
    ( v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_62,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4613,plain,
    ( v2_struct_0(X1_59) = iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | m1_pre_topc(sK7,X1_59) != iProver_top
    | m1_pre_topc(X0_59,sK7) != iProver_top
    | r1_tmap_1(X0_59,sK5,k3_tmap_1(X1_59,sK5,sK7,X0_59,sK8),X0_60) != iProver_top
    | r1_tmap_1(sK7,sK5,sK8,X0_60) = iProver_top
    | v1_tsep_1(X0_59,sK7) != iProver_top
    | m1_subset_1(X0_60,u1_struct_0(X0_59)) != iProver_top
    | m1_subset_1(X0_60,u1_struct_0(sK7)) != iProver_top
    | l1_pre_topc(X1_59) != iProver_top
    | v2_pre_topc(X1_59) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4520,c_58,c_62])).

cnf(c_4614,plain,
    ( r1_tmap_1(X0_59,sK5,k3_tmap_1(X1_59,sK5,sK7,X0_59,sK8),X0_60) != iProver_top
    | r1_tmap_1(sK7,sK5,sK8,X0_60) = iProver_top
    | v1_tsep_1(X0_59,sK7) != iProver_top
    | m1_subset_1(X0_60,u1_struct_0(X0_59)) != iProver_top
    | m1_subset_1(X0_60,u1_struct_0(sK7)) != iProver_top
    | m1_pre_topc(X0_59,sK7) != iProver_top
    | m1_pre_topc(sK7,X1_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | l1_pre_topc(X1_59) != iProver_top
    | v2_pre_topc(X1_59) != iProver_top ),
    inference(renaming,[status(thm)],[c_4613])).

cnf(c_4619,plain,
    ( r1_tmap_1(sK7,sK5,sK8,sK9) = iProver_top
    | v1_tsep_1(sK6,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_pre_topc(sK6,sK7) != iProver_top
    | m1_pre_topc(sK7,sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3338,c_4614])).

cnf(c_49,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_50,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_48,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_51,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_43,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_56,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_40,negated_conjecture,
    ( m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_59,plain,
    ( m1_pre_topc(sK7,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_63,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_31,negated_conjecture,
    ( ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_66,plain,
    ( r1_tmap_1(sK7,sK5,sK8,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_2550,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_3319,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2550])).

cnf(c_3337,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3319,c_2551])).

cnf(c_4623,plain,
    ( m1_pre_topc(sK6,sK7) != iProver_top
    | v1_tsep_1(sK6,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4619,c_50,c_51,c_52,c_56,c_59,c_63,c_66,c_3337])).

cnf(c_4624,plain,
    ( v1_tsep_1(sK6,sK7) != iProver_top
    | m1_pre_topc(sK6,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_4623])).

cnf(c_4625,plain,
    ( ~ v1_tsep_1(sK6,sK7)
    | ~ m1_pre_topc(sK6,sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4624])).

cnf(c_2544,negated_conjecture,
    ( m1_pre_topc(sK6,sK4) ),
    inference(subtyping,[status(esa)],[c_42])).

cnf(c_3324,plain,
    ( m1_pre_topc(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2544])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2575,plain,
    ( ~ m1_pre_topc(X0_59,X1_59)
    | ~ l1_pre_topc(X1_59)
    | ~ v2_pre_topc(X1_59)
    | v2_pre_topc(X0_59) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3295,plain,
    ( m1_pre_topc(X0_59,X1_59) != iProver_top
    | l1_pre_topc(X1_59) != iProver_top
    | v2_pre_topc(X1_59) != iProver_top
    | v2_pre_topc(X0_59) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2575])).

cnf(c_3649,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3324,c_3295])).

cnf(c_3650,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_pre_topc(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3649])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30209,c_12415,c_8168,c_6889,c_6669,c_6203,c_5204,c_4645,c_4625,c_4491,c_3650,c_40,c_41,c_42,c_43,c_47,c_48])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:27:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 11.97/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.97/2.00  
% 11.97/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.97/2.00  
% 11.97/2.00  ------  iProver source info
% 11.97/2.00  
% 11.97/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.97/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.97/2.00  git: non_committed_changes: false
% 11.97/2.00  git: last_make_outside_of_git: false
% 11.97/2.00  
% 11.97/2.00  ------ 
% 11.97/2.00  
% 11.97/2.00  ------ Input Options
% 11.97/2.00  
% 11.97/2.00  --out_options                           all
% 11.97/2.00  --tptp_safe_out                         true
% 11.97/2.00  --problem_path                          ""
% 11.97/2.00  --include_path                          ""
% 11.97/2.00  --clausifier                            res/vclausify_rel
% 11.97/2.00  --clausifier_options                    ""
% 11.97/2.00  --stdin                                 false
% 11.97/2.00  --stats_out                             all
% 11.97/2.00  
% 11.97/2.00  ------ General Options
% 11.97/2.00  
% 11.97/2.00  --fof                                   false
% 11.97/2.00  --time_out_real                         305.
% 11.97/2.00  --time_out_virtual                      -1.
% 11.97/2.00  --symbol_type_check                     false
% 11.97/2.00  --clausify_out                          false
% 11.97/2.00  --sig_cnt_out                           false
% 11.97/2.00  --trig_cnt_out                          false
% 11.97/2.00  --trig_cnt_out_tolerance                1.
% 11.97/2.00  --trig_cnt_out_sk_spl                   false
% 11.97/2.00  --abstr_cl_out                          false
% 11.97/2.00  
% 11.97/2.00  ------ Global Options
% 11.97/2.00  
% 11.97/2.00  --schedule                              default
% 11.97/2.00  --add_important_lit                     false
% 11.97/2.00  --prop_solver_per_cl                    1000
% 11.97/2.00  --min_unsat_core                        false
% 11.97/2.00  --soft_assumptions                      false
% 11.97/2.00  --soft_lemma_size                       3
% 11.97/2.00  --prop_impl_unit_size                   0
% 11.97/2.00  --prop_impl_unit                        []
% 11.97/2.00  --share_sel_clauses                     true
% 11.97/2.00  --reset_solvers                         false
% 11.97/2.00  --bc_imp_inh                            [conj_cone]
% 11.97/2.00  --conj_cone_tolerance                   3.
% 11.97/2.00  --extra_neg_conj                        none
% 11.97/2.00  --large_theory_mode                     true
% 11.97/2.00  --prolific_symb_bound                   200
% 11.97/2.00  --lt_threshold                          2000
% 11.97/2.00  --clause_weak_htbl                      true
% 11.97/2.00  --gc_record_bc_elim                     false
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing Options
% 11.97/2.00  
% 11.97/2.00  --preprocessing_flag                    true
% 11.97/2.00  --time_out_prep_mult                    0.1
% 11.97/2.00  --splitting_mode                        input
% 11.97/2.00  --splitting_grd                         true
% 11.97/2.00  --splitting_cvd                         false
% 11.97/2.00  --splitting_cvd_svl                     false
% 11.97/2.00  --splitting_nvd                         32
% 11.97/2.00  --sub_typing                            true
% 11.97/2.00  --prep_gs_sim                           true
% 11.97/2.00  --prep_unflatten                        true
% 11.97/2.00  --prep_res_sim                          true
% 11.97/2.00  --prep_upred                            true
% 11.97/2.00  --prep_sem_filter                       exhaustive
% 11.97/2.00  --prep_sem_filter_out                   false
% 11.97/2.00  --pred_elim                             true
% 11.97/2.00  --res_sim_input                         true
% 11.97/2.00  --eq_ax_congr_red                       true
% 11.97/2.00  --pure_diseq_elim                       true
% 11.97/2.00  --brand_transform                       false
% 11.97/2.00  --non_eq_to_eq                          false
% 11.97/2.00  --prep_def_merge                        true
% 11.97/2.00  --prep_def_merge_prop_impl              false
% 11.97/2.00  --prep_def_merge_mbd                    true
% 11.97/2.00  --prep_def_merge_tr_red                 false
% 11.97/2.00  --prep_def_merge_tr_cl                  false
% 11.97/2.00  --smt_preprocessing                     true
% 11.97/2.00  --smt_ac_axioms                         fast
% 11.97/2.00  --preprocessed_out                      false
% 11.97/2.00  --preprocessed_stats                    false
% 11.97/2.00  
% 11.97/2.00  ------ Abstraction refinement Options
% 11.97/2.00  
% 11.97/2.00  --abstr_ref                             []
% 11.97/2.00  --abstr_ref_prep                        false
% 11.97/2.00  --abstr_ref_until_sat                   false
% 11.97/2.00  --abstr_ref_sig_restrict                funpre
% 11.97/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.97/2.00  --abstr_ref_under                       []
% 11.97/2.00  
% 11.97/2.00  ------ SAT Options
% 11.97/2.00  
% 11.97/2.00  --sat_mode                              false
% 11.97/2.00  --sat_fm_restart_options                ""
% 11.97/2.00  --sat_gr_def                            false
% 11.97/2.00  --sat_epr_types                         true
% 11.97/2.00  --sat_non_cyclic_types                  false
% 11.97/2.00  --sat_finite_models                     false
% 11.97/2.00  --sat_fm_lemmas                         false
% 11.97/2.00  --sat_fm_prep                           false
% 11.97/2.00  --sat_fm_uc_incr                        true
% 11.97/2.00  --sat_out_model                         small
% 11.97/2.00  --sat_out_clauses                       false
% 11.97/2.00  
% 11.97/2.00  ------ QBF Options
% 11.97/2.00  
% 11.97/2.00  --qbf_mode                              false
% 11.97/2.00  --qbf_elim_univ                         false
% 11.97/2.00  --qbf_dom_inst                          none
% 11.97/2.00  --qbf_dom_pre_inst                      false
% 11.97/2.00  --qbf_sk_in                             false
% 11.97/2.00  --qbf_pred_elim                         true
% 11.97/2.00  --qbf_split                             512
% 11.97/2.00  
% 11.97/2.00  ------ BMC1 Options
% 11.97/2.00  
% 11.97/2.00  --bmc1_incremental                      false
% 11.97/2.00  --bmc1_axioms                           reachable_all
% 11.97/2.00  --bmc1_min_bound                        0
% 11.97/2.00  --bmc1_max_bound                        -1
% 11.97/2.00  --bmc1_max_bound_default                -1
% 11.97/2.00  --bmc1_symbol_reachability              true
% 11.97/2.00  --bmc1_property_lemmas                  false
% 11.97/2.00  --bmc1_k_induction                      false
% 11.97/2.00  --bmc1_non_equiv_states                 false
% 11.97/2.00  --bmc1_deadlock                         false
% 11.97/2.00  --bmc1_ucm                              false
% 11.97/2.00  --bmc1_add_unsat_core                   none
% 11.97/2.00  --bmc1_unsat_core_children              false
% 11.97/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.97/2.00  --bmc1_out_stat                         full
% 11.97/2.00  --bmc1_ground_init                      false
% 11.97/2.00  --bmc1_pre_inst_next_state              false
% 11.97/2.00  --bmc1_pre_inst_state                   false
% 11.97/2.00  --bmc1_pre_inst_reach_state             false
% 11.97/2.00  --bmc1_out_unsat_core                   false
% 11.97/2.00  --bmc1_aig_witness_out                  false
% 11.97/2.00  --bmc1_verbose                          false
% 11.97/2.00  --bmc1_dump_clauses_tptp                false
% 11.97/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.97/2.00  --bmc1_dump_file                        -
% 11.97/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.97/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.97/2.00  --bmc1_ucm_extend_mode                  1
% 11.97/2.00  --bmc1_ucm_init_mode                    2
% 11.97/2.00  --bmc1_ucm_cone_mode                    none
% 11.97/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.97/2.00  --bmc1_ucm_relax_model                  4
% 11.97/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.97/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.97/2.00  --bmc1_ucm_layered_model                none
% 11.97/2.00  --bmc1_ucm_max_lemma_size               10
% 11.97/2.00  
% 11.97/2.00  ------ AIG Options
% 11.97/2.00  
% 11.97/2.00  --aig_mode                              false
% 11.97/2.00  
% 11.97/2.00  ------ Instantiation Options
% 11.97/2.00  
% 11.97/2.00  --instantiation_flag                    true
% 11.97/2.00  --inst_sos_flag                         true
% 11.97/2.00  --inst_sos_phase                        true
% 11.97/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.97/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.97/2.00  --inst_lit_sel_side                     num_symb
% 11.97/2.00  --inst_solver_per_active                1400
% 11.97/2.00  --inst_solver_calls_frac                1.
% 11.97/2.00  --inst_passive_queue_type               priority_queues
% 11.97/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.97/2.00  --inst_passive_queues_freq              [25;2]
% 11.97/2.00  --inst_dismatching                      true
% 11.97/2.00  --inst_eager_unprocessed_to_passive     true
% 11.97/2.00  --inst_prop_sim_given                   true
% 11.97/2.00  --inst_prop_sim_new                     false
% 11.97/2.00  --inst_subs_new                         false
% 11.97/2.00  --inst_eq_res_simp                      false
% 11.97/2.00  --inst_subs_given                       false
% 11.97/2.00  --inst_orphan_elimination               true
% 11.97/2.00  --inst_learning_loop_flag               true
% 11.97/2.00  --inst_learning_start                   3000
% 11.97/2.00  --inst_learning_factor                  2
% 11.97/2.00  --inst_start_prop_sim_after_learn       3
% 11.97/2.00  --inst_sel_renew                        solver
% 11.97/2.00  --inst_lit_activity_flag                true
% 11.97/2.00  --inst_restr_to_given                   false
% 11.97/2.00  --inst_activity_threshold               500
% 11.97/2.00  --inst_out_proof                        true
% 11.97/2.00  
% 11.97/2.00  ------ Resolution Options
% 11.97/2.00  
% 11.97/2.00  --resolution_flag                       true
% 11.97/2.00  --res_lit_sel                           adaptive
% 11.97/2.00  --res_lit_sel_side                      none
% 11.97/2.00  --res_ordering                          kbo
% 11.97/2.00  --res_to_prop_solver                    active
% 11.97/2.00  --res_prop_simpl_new                    false
% 11.97/2.00  --res_prop_simpl_given                  true
% 11.97/2.00  --res_passive_queue_type                priority_queues
% 11.97/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.97/2.00  --res_passive_queues_freq               [15;5]
% 11.97/2.00  --res_forward_subs                      full
% 11.97/2.00  --res_backward_subs                     full
% 11.97/2.00  --res_forward_subs_resolution           true
% 11.97/2.00  --res_backward_subs_resolution          true
% 11.97/2.00  --res_orphan_elimination                true
% 11.97/2.00  --res_time_limit                        2.
% 11.97/2.00  --res_out_proof                         true
% 11.97/2.00  
% 11.97/2.00  ------ Superposition Options
% 11.97/2.00  
% 11.97/2.00  --superposition_flag                    true
% 11.97/2.00  --sup_passive_queue_type                priority_queues
% 11.97/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.97/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.97/2.00  --demod_completeness_check              fast
% 11.97/2.00  --demod_use_ground                      true
% 11.97/2.00  --sup_to_prop_solver                    passive
% 11.97/2.00  --sup_prop_simpl_new                    true
% 11.97/2.00  --sup_prop_simpl_given                  true
% 11.97/2.00  --sup_fun_splitting                     true
% 11.97/2.00  --sup_smt_interval                      50000
% 11.97/2.00  
% 11.97/2.00  ------ Superposition Simplification Setup
% 11.97/2.00  
% 11.97/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.97/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.97/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.97/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.97/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.97/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.97/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.97/2.00  --sup_immed_triv                        [TrivRules]
% 11.97/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.97/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.97/2.00  --sup_immed_bw_main                     []
% 11.97/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.97/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.97/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.97/2.00  --sup_input_bw                          []
% 11.97/2.00  
% 11.97/2.00  ------ Combination Options
% 11.97/2.00  
% 11.97/2.00  --comb_res_mult                         3
% 11.97/2.00  --comb_sup_mult                         2
% 11.97/2.00  --comb_inst_mult                        10
% 11.97/2.00  
% 11.97/2.00  ------ Debug Options
% 11.97/2.00  
% 11.97/2.00  --dbg_backtrace                         false
% 11.97/2.00  --dbg_dump_prop_clauses                 false
% 11.97/2.00  --dbg_dump_prop_clauses_file            -
% 11.97/2.00  --dbg_out_stat                          false
% 11.97/2.00  ------ Parsing...
% 11.97/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  ------ Proving...
% 11.97/2.00  ------ Problem Properties 
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  clauses                                 44
% 11.97/2.00  conjectures                             17
% 11.97/2.00  EPR                                     17
% 11.97/2.00  Horn                                    34
% 11.97/2.00  unary                                   17
% 11.97/2.00  binary                                  6
% 11.97/2.00  lits                                    152
% 11.97/2.00  lits eq                                 6
% 11.97/2.00  fd_pure                                 0
% 11.97/2.00  fd_pseudo                               0
% 11.97/2.00  fd_cond                                 0
% 11.97/2.00  fd_pseudo_cond                          0
% 11.97/2.00  AC symbols                              0
% 11.97/2.00  
% 11.97/2.00  ------ Schedule dynamic 5 is on 
% 11.97/2.00  
% 11.97/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ 
% 11.97/2.00  Current options:
% 11.97/2.00  ------ 
% 11.97/2.00  
% 11.97/2.00  ------ Input Options
% 11.97/2.00  
% 11.97/2.00  --out_options                           all
% 11.97/2.00  --tptp_safe_out                         true
% 11.97/2.00  --problem_path                          ""
% 11.97/2.00  --include_path                          ""
% 11.97/2.00  --clausifier                            res/vclausify_rel
% 11.97/2.00  --clausifier_options                    ""
% 11.97/2.00  --stdin                                 false
% 11.97/2.00  --stats_out                             all
% 11.97/2.00  
% 11.97/2.00  ------ General Options
% 11.97/2.00  
% 11.97/2.00  --fof                                   false
% 11.97/2.00  --time_out_real                         305.
% 11.97/2.00  --time_out_virtual                      -1.
% 11.97/2.00  --symbol_type_check                     false
% 11.97/2.00  --clausify_out                          false
% 11.97/2.00  --sig_cnt_out                           false
% 11.97/2.00  --trig_cnt_out                          false
% 11.97/2.00  --trig_cnt_out_tolerance                1.
% 11.97/2.00  --trig_cnt_out_sk_spl                   false
% 11.97/2.00  --abstr_cl_out                          false
% 11.97/2.00  
% 11.97/2.00  ------ Global Options
% 11.97/2.00  
% 11.97/2.00  --schedule                              default
% 11.97/2.00  --add_important_lit                     false
% 11.97/2.00  --prop_solver_per_cl                    1000
% 11.97/2.00  --min_unsat_core                        false
% 11.97/2.00  --soft_assumptions                      false
% 11.97/2.00  --soft_lemma_size                       3
% 11.97/2.00  --prop_impl_unit_size                   0
% 11.97/2.00  --prop_impl_unit                        []
% 11.97/2.00  --share_sel_clauses                     true
% 11.97/2.00  --reset_solvers                         false
% 11.97/2.00  --bc_imp_inh                            [conj_cone]
% 11.97/2.00  --conj_cone_tolerance                   3.
% 11.97/2.00  --extra_neg_conj                        none
% 11.97/2.00  --large_theory_mode                     true
% 11.97/2.00  --prolific_symb_bound                   200
% 11.97/2.00  --lt_threshold                          2000
% 11.97/2.00  --clause_weak_htbl                      true
% 11.97/2.00  --gc_record_bc_elim                     false
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing Options
% 11.97/2.00  
% 11.97/2.00  --preprocessing_flag                    true
% 11.97/2.00  --time_out_prep_mult                    0.1
% 11.97/2.00  --splitting_mode                        input
% 11.97/2.00  --splitting_grd                         true
% 11.97/2.00  --splitting_cvd                         false
% 11.97/2.00  --splitting_cvd_svl                     false
% 11.97/2.00  --splitting_nvd                         32
% 11.97/2.00  --sub_typing                            true
% 11.97/2.00  --prep_gs_sim                           true
% 11.97/2.00  --prep_unflatten                        true
% 11.97/2.00  --prep_res_sim                          true
% 11.97/2.00  --prep_upred                            true
% 11.97/2.00  --prep_sem_filter                       exhaustive
% 11.97/2.00  --prep_sem_filter_out                   false
% 11.97/2.00  --pred_elim                             true
% 11.97/2.00  --res_sim_input                         true
% 11.97/2.00  --eq_ax_congr_red                       true
% 11.97/2.00  --pure_diseq_elim                       true
% 11.97/2.00  --brand_transform                       false
% 11.97/2.00  --non_eq_to_eq                          false
% 11.97/2.00  --prep_def_merge                        true
% 11.97/2.00  --prep_def_merge_prop_impl              false
% 11.97/2.00  --prep_def_merge_mbd                    true
% 11.97/2.00  --prep_def_merge_tr_red                 false
% 11.97/2.00  --prep_def_merge_tr_cl                  false
% 11.97/2.00  --smt_preprocessing                     true
% 11.97/2.00  --smt_ac_axioms                         fast
% 11.97/2.00  --preprocessed_out                      false
% 11.97/2.00  --preprocessed_stats                    false
% 11.97/2.00  
% 11.97/2.00  ------ Abstraction refinement Options
% 11.97/2.00  
% 11.97/2.00  --abstr_ref                             []
% 11.97/2.00  --abstr_ref_prep                        false
% 11.97/2.00  --abstr_ref_until_sat                   false
% 11.97/2.00  --abstr_ref_sig_restrict                funpre
% 11.97/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.97/2.00  --abstr_ref_under                       []
% 11.97/2.00  
% 11.97/2.00  ------ SAT Options
% 11.97/2.00  
% 11.97/2.00  --sat_mode                              false
% 11.97/2.00  --sat_fm_restart_options                ""
% 11.97/2.00  --sat_gr_def                            false
% 11.97/2.00  --sat_epr_types                         true
% 11.97/2.00  --sat_non_cyclic_types                  false
% 11.97/2.00  --sat_finite_models                     false
% 11.97/2.00  --sat_fm_lemmas                         false
% 11.97/2.00  --sat_fm_prep                           false
% 11.97/2.00  --sat_fm_uc_incr                        true
% 11.97/2.00  --sat_out_model                         small
% 11.97/2.00  --sat_out_clauses                       false
% 11.97/2.00  
% 11.97/2.00  ------ QBF Options
% 11.97/2.00  
% 11.97/2.00  --qbf_mode                              false
% 11.97/2.00  --qbf_elim_univ                         false
% 11.97/2.00  --qbf_dom_inst                          none
% 11.97/2.00  --qbf_dom_pre_inst                      false
% 11.97/2.00  --qbf_sk_in                             false
% 11.97/2.00  --qbf_pred_elim                         true
% 11.97/2.00  --qbf_split                             512
% 11.97/2.00  
% 11.97/2.00  ------ BMC1 Options
% 11.97/2.00  
% 11.97/2.00  --bmc1_incremental                      false
% 11.97/2.00  --bmc1_axioms                           reachable_all
% 11.97/2.00  --bmc1_min_bound                        0
% 11.97/2.00  --bmc1_max_bound                        -1
% 11.97/2.00  --bmc1_max_bound_default                -1
% 11.97/2.00  --bmc1_symbol_reachability              true
% 11.97/2.00  --bmc1_property_lemmas                  false
% 11.97/2.00  --bmc1_k_induction                      false
% 11.97/2.00  --bmc1_non_equiv_states                 false
% 11.97/2.00  --bmc1_deadlock                         false
% 11.97/2.00  --bmc1_ucm                              false
% 11.97/2.00  --bmc1_add_unsat_core                   none
% 11.97/2.00  --bmc1_unsat_core_children              false
% 11.97/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.97/2.00  --bmc1_out_stat                         full
% 11.97/2.00  --bmc1_ground_init                      false
% 11.97/2.00  --bmc1_pre_inst_next_state              false
% 11.97/2.00  --bmc1_pre_inst_state                   false
% 11.97/2.00  --bmc1_pre_inst_reach_state             false
% 11.97/2.00  --bmc1_out_unsat_core                   false
% 11.97/2.00  --bmc1_aig_witness_out                  false
% 11.97/2.00  --bmc1_verbose                          false
% 11.97/2.00  --bmc1_dump_clauses_tptp                false
% 11.97/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.97/2.00  --bmc1_dump_file                        -
% 11.97/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.97/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.97/2.00  --bmc1_ucm_extend_mode                  1
% 11.97/2.00  --bmc1_ucm_init_mode                    2
% 11.97/2.00  --bmc1_ucm_cone_mode                    none
% 11.97/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.97/2.00  --bmc1_ucm_relax_model                  4
% 11.97/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.97/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.97/2.00  --bmc1_ucm_layered_model                none
% 11.97/2.00  --bmc1_ucm_max_lemma_size               10
% 11.97/2.00  
% 11.97/2.00  ------ AIG Options
% 11.97/2.00  
% 11.97/2.00  --aig_mode                              false
% 11.97/2.00  
% 11.97/2.00  ------ Instantiation Options
% 11.97/2.00  
% 11.97/2.00  --instantiation_flag                    true
% 11.97/2.00  --inst_sos_flag                         true
% 11.97/2.00  --inst_sos_phase                        true
% 11.97/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.97/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.97/2.00  --inst_lit_sel_side                     none
% 11.97/2.00  --inst_solver_per_active                1400
% 11.97/2.00  --inst_solver_calls_frac                1.
% 11.97/2.00  --inst_passive_queue_type               priority_queues
% 11.97/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.97/2.00  --inst_passive_queues_freq              [25;2]
% 11.97/2.00  --inst_dismatching                      true
% 11.97/2.00  --inst_eager_unprocessed_to_passive     true
% 11.97/2.00  --inst_prop_sim_given                   true
% 11.97/2.00  --inst_prop_sim_new                     false
% 11.97/2.00  --inst_subs_new                         false
% 11.97/2.00  --inst_eq_res_simp                      false
% 11.97/2.00  --inst_subs_given                       false
% 11.97/2.00  --inst_orphan_elimination               true
% 11.97/2.00  --inst_learning_loop_flag               true
% 11.97/2.00  --inst_learning_start                   3000
% 11.97/2.00  --inst_learning_factor                  2
% 11.97/2.00  --inst_start_prop_sim_after_learn       3
% 11.97/2.00  --inst_sel_renew                        solver
% 11.97/2.00  --inst_lit_activity_flag                true
% 11.97/2.00  --inst_restr_to_given                   false
% 11.97/2.00  --inst_activity_threshold               500
% 11.97/2.00  --inst_out_proof                        true
% 11.97/2.00  
% 11.97/2.00  ------ Resolution Options
% 11.97/2.00  
% 11.97/2.00  --resolution_flag                       false
% 11.97/2.00  --res_lit_sel                           adaptive
% 11.97/2.00  --res_lit_sel_side                      none
% 11.97/2.00  --res_ordering                          kbo
% 11.97/2.00  --res_to_prop_solver                    active
% 11.97/2.00  --res_prop_simpl_new                    false
% 11.97/2.00  --res_prop_simpl_given                  true
% 11.97/2.00  --res_passive_queue_type                priority_queues
% 11.97/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.97/2.00  --res_passive_queues_freq               [15;5]
% 11.97/2.00  --res_forward_subs                      full
% 11.97/2.00  --res_backward_subs                     full
% 11.97/2.00  --res_forward_subs_resolution           true
% 11.97/2.00  --res_backward_subs_resolution          true
% 11.97/2.00  --res_orphan_elimination                true
% 11.97/2.00  --res_time_limit                        2.
% 11.97/2.00  --res_out_proof                         true
% 11.97/2.00  
% 11.97/2.00  ------ Superposition Options
% 11.97/2.00  
% 11.97/2.00  --superposition_flag                    true
% 11.97/2.00  --sup_passive_queue_type                priority_queues
% 11.97/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.97/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.97/2.00  --demod_completeness_check              fast
% 11.97/2.00  --demod_use_ground                      true
% 11.97/2.00  --sup_to_prop_solver                    passive
% 11.97/2.00  --sup_prop_simpl_new                    true
% 11.97/2.00  --sup_prop_simpl_given                  true
% 11.97/2.00  --sup_fun_splitting                     true
% 11.97/2.00  --sup_smt_interval                      50000
% 11.97/2.00  
% 11.97/2.00  ------ Superposition Simplification Setup
% 11.97/2.00  
% 11.97/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.97/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.97/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.97/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.97/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.97/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.97/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.97/2.00  --sup_immed_triv                        [TrivRules]
% 11.97/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.97/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.97/2.00  --sup_immed_bw_main                     []
% 11.97/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.97/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.97/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.97/2.00  --sup_input_bw                          []
% 11.97/2.00  
% 11.97/2.00  ------ Combination Options
% 11.97/2.00  
% 11.97/2.00  --comb_res_mult                         3
% 11.97/2.00  --comb_sup_mult                         2
% 11.97/2.00  --comb_inst_mult                        10
% 11.97/2.00  
% 11.97/2.00  ------ Debug Options
% 11.97/2.00  
% 11.97/2.00  --dbg_backtrace                         false
% 11.97/2.00  --dbg_dump_prop_clauses                 false
% 11.97/2.00  --dbg_dump_prop_clauses_file            -
% 11.97/2.00  --dbg_out_stat                          false
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  % SZS status Theorem for theBenchmark.p
% 11.97/2.00  
% 11.97/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.97/2.00  
% 11.97/2.00  fof(f9,axiom,(
% 11.97/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f30,plain,(
% 11.97/2.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.97/2.00    inference(ennf_transformation,[],[f9])).
% 11.97/2.00  
% 11.97/2.00  fof(f31,plain,(
% 11.97/2.00    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.97/2.00    inference(flattening,[],[f30])).
% 11.97/2.00  
% 11.97/2.00  fof(f89,plain,(
% 11.97/2.00    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.97/2.00    inference(cnf_transformation,[],[f31])).
% 11.97/2.00  
% 11.97/2.00  fof(f2,axiom,(
% 11.97/2.00    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f17,plain,(
% 11.97/2.00    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 11.97/2.00    inference(rectify,[],[f2])).
% 11.97/2.00  
% 11.97/2.00  fof(f21,plain,(
% 11.97/2.00    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 11.97/2.00    inference(ennf_transformation,[],[f17])).
% 11.97/2.00  
% 11.97/2.00  fof(f22,plain,(
% 11.97/2.00    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 11.97/2.00    inference(flattening,[],[f21])).
% 11.97/2.00  
% 11.97/2.00  fof(f41,plain,(
% 11.97/2.00    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.97/2.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 11.97/2.00  
% 11.97/2.00  fof(f42,plain,(
% 11.97/2.00    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 11.97/2.00    inference(definition_folding,[],[f22,f41])).
% 11.97/2.00  
% 11.97/2.00  fof(f48,plain,(
% 11.97/2.00    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 11.97/2.01    inference(nnf_transformation,[],[f42])).
% 11.97/2.01  
% 11.97/2.01  fof(f49,plain,(
% 11.97/2.01    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 11.97/2.01    inference(flattening,[],[f48])).
% 11.97/2.01  
% 11.97/2.01  fof(f50,plain,(
% 11.97/2.01    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 11.97/2.01    inference(rectify,[],[f49])).
% 11.97/2.01  
% 11.97/2.01  fof(f51,plain,(
% 11.97/2.01    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 11.97/2.01    introduced(choice_axiom,[])).
% 11.97/2.01  
% 11.97/2.01  fof(f52,plain,(
% 11.97/2.01    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 11.97/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f50,f51])).
% 11.97/2.01  
% 11.97/2.01  fof(f73,plain,(
% 11.97/2.01    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 11.97/2.01    inference(cnf_transformation,[],[f52])).
% 11.97/2.01  
% 11.97/2.01  fof(f12,axiom,(
% 11.97/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 11.97/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.01  
% 11.97/2.01  fof(f34,plain,(
% 11.97/2.01    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.97/2.01    inference(ennf_transformation,[],[f12])).
% 11.97/2.01  
% 11.97/2.01  fof(f93,plain,(
% 11.97/2.01    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.97/2.01    inference(cnf_transformation,[],[f34])).
% 11.97/2.01  
% 11.97/2.01  fof(f3,axiom,(
% 11.97/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 11.97/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.01  
% 11.97/2.01  fof(f23,plain,(
% 11.97/2.01    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.97/2.01    inference(ennf_transformation,[],[f3])).
% 11.97/2.01  
% 11.97/2.01  fof(f53,plain,(
% 11.97/2.01    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.97/2.01    inference(nnf_transformation,[],[f23])).
% 11.97/2.01  
% 11.97/2.01  fof(f80,plain,(
% 11.97/2.01    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.97/2.01    inference(cnf_transformation,[],[f53])).
% 11.97/2.01  
% 11.97/2.01  fof(f8,axiom,(
% 11.97/2.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 11.97/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.01  
% 11.97/2.01  fof(f28,plain,(
% 11.97/2.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.97/2.01    inference(ennf_transformation,[],[f8])).
% 11.97/2.01  
% 11.97/2.01  fof(f29,plain,(
% 11.97/2.01    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.97/2.01    inference(flattening,[],[f28])).
% 11.97/2.01  
% 11.97/2.01  fof(f55,plain,(
% 11.97/2.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.97/2.01    inference(nnf_transformation,[],[f29])).
% 11.97/2.01  
% 11.97/2.01  fof(f56,plain,(
% 11.97/2.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.97/2.01    inference(flattening,[],[f55])).
% 11.97/2.01  
% 11.97/2.01  fof(f87,plain,(
% 11.97/2.01    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.97/2.01    inference(cnf_transformation,[],[f56])).
% 11.97/2.01  
% 11.97/2.01  fof(f117,plain,(
% 11.97/2.01    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.97/2.01    inference(equality_resolution,[],[f87])).
% 11.97/2.01  
% 11.97/2.01  fof(f10,axiom,(
% 11.97/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.97/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.01  
% 11.97/2.01  fof(f32,plain,(
% 11.97/2.01    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.97/2.01    inference(ennf_transformation,[],[f10])).
% 11.97/2.01  
% 11.97/2.01  fof(f91,plain,(
% 11.97/2.01    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.97/2.01    inference(cnf_transformation,[],[f32])).
% 11.97/2.01  
% 11.97/2.01  fof(f11,axiom,(
% 11.97/2.01    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 11.97/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.01  
% 11.97/2.01  fof(f33,plain,(
% 11.97/2.01    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 11.97/2.01    inference(ennf_transformation,[],[f11])).
% 11.97/2.01  
% 11.97/2.01  fof(f92,plain,(
% 11.97/2.01    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 11.97/2.01    inference(cnf_transformation,[],[f33])).
% 11.97/2.01  
% 11.97/2.01  fof(f15,conjecture,(
% 11.97/2.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 11.97/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.01  
% 11.97/2.01  fof(f16,negated_conjecture,(
% 11.97/2.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 11.97/2.01    inference(negated_conjecture,[],[f15])).
% 11.97/2.01  
% 11.97/2.01  fof(f39,plain,(
% 11.97/2.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 11.97/2.01    inference(ennf_transformation,[],[f16])).
% 11.97/2.01  
% 11.97/2.01  fof(f40,plain,(
% 11.97/2.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.97/2.01    inference(flattening,[],[f39])).
% 11.97/2.01  
% 11.97/2.01  fof(f64,plain,(
% 11.97/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK10) & sK10 = X5 & m1_subset_1(sK10,u1_struct_0(X2)))) )),
% 11.97/2.01    introduced(choice_axiom,[])).
% 11.97/2.01  
% 11.97/2.01  fof(f63,plain,(
% 11.97/2.01    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK9) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK9 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK9,u1_struct_0(X3)))) )),
% 11.97/2.01    introduced(choice_axiom,[])).
% 11.97/2.01  
% 11.97/2.01  fof(f62,plain,(
% 11.97/2.01    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK8,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK8),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK8,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK8))) )),
% 11.97/2.01    introduced(choice_axiom,[])).
% 11.97/2.01  
% 11.97/2.01  fof(f61,plain,(
% 11.97/2.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK7,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK7,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK7))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK7 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK7,X0) & ~v2_struct_0(sK7))) )),
% 11.97/2.01    introduced(choice_axiom,[])).
% 11.97/2.01  
% 11.97/2.01  fof(f60,plain,(
% 11.97/2.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK6,X1,k3_tmap_1(X0,X1,X3,sK6,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK6))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 11.97/2.01    introduced(choice_axiom,[])).
% 11.97/2.01  
% 11.97/2.01  fof(f59,plain,(
% 11.97/2.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK5,X4,X5) & r1_tmap_1(X2,sK5,k3_tmap_1(X0,sK5,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))) )),
% 11.97/2.01    introduced(choice_axiom,[])).
% 11.97/2.01  
% 11.97/2.01  fof(f58,plain,(
% 11.97/2.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK4,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 11.97/2.01    introduced(choice_axiom,[])).
% 11.97/2.01  
% 11.97/2.01  fof(f65,plain,(
% 11.97/2.01    ((((((~r1_tmap_1(sK7,sK5,sK8,sK9) & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) & sK9 = sK10 & m1_subset_1(sK10,u1_struct_0(sK6))) & m1_subset_1(sK9,u1_struct_0(sK7))) & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(sK8)) & m1_pre_topc(sK7,sK4) & ~v2_struct_0(sK7)) & m1_pre_topc(sK6,sK4) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 11.97/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f40,f64,f63,f62,f61,f60,f59,f58])).
% 11.97/2.01  
% 11.97/2.01  fof(f110,plain,(
% 11.97/2.01    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7),
% 11.97/2.01    inference(cnf_transformation,[],[f65])).
% 11.97/2.01  
% 11.97/2.01  fof(f6,axiom,(
% 11.97/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 11.97/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.01  
% 11.97/2.01  fof(f26,plain,(
% 11.97/2.01    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 11.97/2.01    inference(ennf_transformation,[],[f6])).
% 11.97/2.01  
% 11.97/2.01  fof(f54,plain,(
% 11.97/2.01    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 11.97/2.01    inference(nnf_transformation,[],[f26])).
% 11.97/2.01  
% 11.97/2.01  fof(f83,plain,(
% 11.97/2.01    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 11.97/2.01    inference(cnf_transformation,[],[f54])).
% 11.97/2.01  
% 11.97/2.01  fof(f4,axiom,(
% 11.97/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 11.97/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.01  
% 11.97/2.01  fof(f24,plain,(
% 11.97/2.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.97/2.01    inference(ennf_transformation,[],[f4])).
% 11.97/2.01  
% 11.97/2.01  fof(f81,plain,(
% 11.97/2.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.97/2.01    inference(cnf_transformation,[],[f24])).
% 11.97/2.01  
% 11.97/2.01  fof(f99,plain,(
% 11.97/2.01    l1_pre_topc(sK4)),
% 11.97/2.01    inference(cnf_transformation,[],[f65])).
% 11.97/2.01  
% 11.97/2.01  fof(f104,plain,(
% 11.97/2.01    m1_pre_topc(sK6,sK4)),
% 11.97/2.01    inference(cnf_transformation,[],[f65])).
% 11.97/2.01  
% 11.97/2.01  fof(f5,axiom,(
% 11.97/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 11.97/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.01  
% 11.97/2.01  fof(f25,plain,(
% 11.97/2.01    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 11.97/2.01    inference(ennf_transformation,[],[f5])).
% 11.97/2.01  
% 11.97/2.01  fof(f82,plain,(
% 11.97/2.01    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 11.97/2.01    inference(cnf_transformation,[],[f25])).
% 11.97/2.01  
% 11.97/2.01  fof(f114,plain,(
% 11.97/2.01    r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)),
% 11.97/2.01    inference(cnf_transformation,[],[f65])).
% 11.97/2.01  
% 11.97/2.01  fof(f113,plain,(
% 11.97/2.01    sK9 = sK10),
% 11.97/2.01    inference(cnf_transformation,[],[f65])).
% 11.97/2.01  
% 11.97/2.01  fof(f14,axiom,(
% 11.97/2.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 11.97/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.01  
% 11.97/2.01  fof(f37,plain,(
% 11.97/2.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.97/2.01    inference(ennf_transformation,[],[f14])).
% 11.97/2.01  
% 11.97/2.01  fof(f38,plain,(
% 11.97/2.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.97/2.01    inference(flattening,[],[f37])).
% 11.97/2.01  
% 11.97/2.01  fof(f57,plain,(
% 11.97/2.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.97/2.01    inference(nnf_transformation,[],[f38])).
% 11.97/2.01  
% 11.97/2.01  fof(f96,plain,(
% 11.97/2.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.97/2.01    inference(cnf_transformation,[],[f57])).
% 11.97/2.01  
% 11.97/2.01  fof(f119,plain,(
% 11.97/2.01    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.97/2.01    inference(equality_resolution,[],[f96])).
% 11.97/2.01  
% 11.97/2.01  fof(f108,plain,(
% 11.97/2.01    v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))),
% 11.97/2.01    inference(cnf_transformation,[],[f65])).
% 11.97/2.01  
% 11.97/2.01  fof(f107,plain,(
% 11.97/2.01    v1_funct_1(sK8)),
% 11.97/2.01    inference(cnf_transformation,[],[f65])).
% 11.97/2.01  
% 11.97/2.01  fof(f13,axiom,(
% 11.97/2.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 11.97/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.01  
% 11.97/2.01  fof(f35,plain,(
% 11.97/2.01    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.97/2.01    inference(ennf_transformation,[],[f13])).
% 11.97/2.01  
% 11.97/2.01  fof(f36,plain,(
% 11.97/2.01    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.97/2.01    inference(flattening,[],[f35])).
% 11.97/2.01  
% 11.97/2.01  fof(f94,plain,(
% 11.97/2.01    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.97/2.01    inference(cnf_transformation,[],[f36])).
% 11.97/2.01  
% 11.97/2.01  fof(f100,plain,(
% 11.97/2.01    ~v2_struct_0(sK5)),
% 11.97/2.01    inference(cnf_transformation,[],[f65])).
% 11.97/2.01  
% 11.97/2.01  fof(f101,plain,(
% 11.97/2.01    v2_pre_topc(sK5)),
% 11.97/2.01    inference(cnf_transformation,[],[f65])).
% 11.97/2.01  
% 11.97/2.01  fof(f102,plain,(
% 11.97/2.01    l1_pre_topc(sK5)),
% 11.97/2.01    inference(cnf_transformation,[],[f65])).
% 11.97/2.01  
% 11.97/2.01  fof(f105,plain,(
% 11.97/2.01    ~v2_struct_0(sK7)),
% 11.97/2.01    inference(cnf_transformation,[],[f65])).
% 11.97/2.01  
% 11.97/2.01  fof(f109,plain,(
% 11.97/2.01    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))),
% 11.97/2.01    inference(cnf_transformation,[],[f65])).
% 11.97/2.01  
% 11.97/2.01  fof(f97,plain,(
% 11.97/2.01    ~v2_struct_0(sK4)),
% 11.97/2.01    inference(cnf_transformation,[],[f65])).
% 11.97/2.01  
% 11.97/2.01  fof(f98,plain,(
% 11.97/2.01    v2_pre_topc(sK4)),
% 11.97/2.01    inference(cnf_transformation,[],[f65])).
% 11.97/2.01  
% 11.97/2.01  fof(f103,plain,(
% 11.97/2.01    ~v2_struct_0(sK6)),
% 11.97/2.01    inference(cnf_transformation,[],[f65])).
% 11.97/2.01  
% 11.97/2.01  fof(f106,plain,(
% 11.97/2.01    m1_pre_topc(sK7,sK4)),
% 11.97/2.01    inference(cnf_transformation,[],[f65])).
% 11.97/2.01  
% 11.97/2.01  fof(f111,plain,(
% 11.97/2.01    m1_subset_1(sK9,u1_struct_0(sK7))),
% 11.97/2.01    inference(cnf_transformation,[],[f65])).
% 11.97/2.01  
% 11.97/2.01  fof(f115,plain,(
% 11.97/2.01    ~r1_tmap_1(sK7,sK5,sK8,sK9)),
% 11.97/2.01    inference(cnf_transformation,[],[f65])).
% 11.97/2.01  
% 11.97/2.01  fof(f112,plain,(
% 11.97/2.01    m1_subset_1(sK10,u1_struct_0(sK6))),
% 11.97/2.01    inference(cnf_transformation,[],[f65])).
% 11.97/2.01  
% 11.97/2.01  fof(f1,axiom,(
% 11.97/2.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 11.97/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.01  
% 11.97/2.01  fof(f19,plain,(
% 11.97/2.01    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.97/2.01    inference(ennf_transformation,[],[f1])).
% 11.97/2.01  
% 11.97/2.01  fof(f20,plain,(
% 11.97/2.01    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.97/2.01    inference(flattening,[],[f19])).
% 11.97/2.01  
% 11.97/2.01  fof(f66,plain,(
% 11.97/2.01    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.97/2.01    inference(cnf_transformation,[],[f20])).
% 11.97/2.01  
% 11.97/2.01  cnf(c_24,plain,
% 11.97/2.01      ( ~ v1_tsep_1(X0,X1)
% 11.97/2.01      | v1_tsep_1(X0,X2)
% 11.97/2.01      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 11.97/2.01      | ~ m1_pre_topc(X0,X1)
% 11.97/2.01      | ~ m1_pre_topc(X2,X1)
% 11.97/2.01      | v2_struct_0(X1)
% 11.97/2.01      | v2_struct_0(X2)
% 11.97/2.01      | ~ l1_pre_topc(X1)
% 11.97/2.01      | ~ v2_pre_topc(X1) ),
% 11.97/2.01      inference(cnf_transformation,[],[f89]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_2558,plain,
% 11.97/2.01      ( ~ v1_tsep_1(X0_59,X1_59)
% 11.97/2.01      | v1_tsep_1(X0_59,X2_59)
% 11.97/2.01      | ~ r1_tarski(u1_struct_0(X0_59),u1_struct_0(X2_59))
% 11.97/2.01      | ~ m1_pre_topc(X0_59,X1_59)
% 11.97/2.01      | ~ m1_pre_topc(X2_59,X1_59)
% 11.97/2.01      | v2_struct_0(X1_59)
% 11.97/2.01      | v2_struct_0(X2_59)
% 11.97/2.01      | ~ l1_pre_topc(X1_59)
% 11.97/2.01      | ~ v2_pre_topc(X1_59) ),
% 11.97/2.01      inference(subtyping,[status(esa)],[c_24]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_3492,plain,
% 11.97/2.01      ( ~ v1_tsep_1(X0_59,X1_59)
% 11.97/2.01      | v1_tsep_1(X0_59,sK7)
% 11.97/2.01      | ~ r1_tarski(u1_struct_0(X0_59),u1_struct_0(sK7))
% 11.97/2.01      | ~ m1_pre_topc(X0_59,X1_59)
% 11.97/2.01      | ~ m1_pre_topc(sK7,X1_59)
% 11.97/2.01      | v2_struct_0(X1_59)
% 11.97/2.01      | v2_struct_0(sK7)
% 11.97/2.01      | ~ l1_pre_topc(X1_59)
% 11.97/2.01      | ~ v2_pre_topc(X1_59) ),
% 11.97/2.01      inference(instantiation,[status(thm)],[c_2558]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_7638,plain,
% 11.97/2.01      ( ~ v1_tsep_1(X0_59,sK6)
% 11.97/2.01      | v1_tsep_1(X0_59,sK7)
% 11.97/2.01      | ~ r1_tarski(u1_struct_0(X0_59),u1_struct_0(sK7))
% 11.97/2.01      | ~ m1_pre_topc(X0_59,sK6)
% 11.97/2.01      | ~ m1_pre_topc(sK7,sK6)
% 11.97/2.01      | v2_struct_0(sK6)
% 11.97/2.01      | v2_struct_0(sK7)
% 11.97/2.01      | ~ l1_pre_topc(sK6)
% 11.97/2.01      | ~ v2_pre_topc(sK6) ),
% 11.97/2.01      inference(instantiation,[status(thm)],[c_3492]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_30209,plain,
% 11.97/2.01      ( ~ v1_tsep_1(sK6,sK6)
% 11.97/2.01      | v1_tsep_1(sK6,sK7)
% 11.97/2.01      | ~ r1_tarski(u1_struct_0(sK6),u1_struct_0(sK7))
% 11.97/2.01      | ~ m1_pre_topc(sK6,sK6)
% 11.97/2.01      | ~ m1_pre_topc(sK7,sK6)
% 11.97/2.01      | v2_struct_0(sK6)
% 11.97/2.01      | v2_struct_0(sK7)
% 11.97/2.01      | ~ l1_pre_topc(sK6)
% 11.97/2.01      | ~ v2_pre_topc(sK6) ),
% 11.97/2.01      inference(instantiation,[status(thm)],[c_7638]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_12,plain,
% 11.97/2.01      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 11.97/2.01      | ~ l1_pre_topc(X0)
% 11.97/2.01      | ~ v2_pre_topc(X0) ),
% 11.97/2.01      inference(cnf_transformation,[],[f73]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_2563,plain,
% 11.97/2.01      ( r2_hidden(u1_struct_0(X0_59),u1_pre_topc(X0_59))
% 11.97/2.01      | ~ l1_pre_topc(X0_59)
% 11.97/2.01      | ~ v2_pre_topc(X0_59) ),
% 11.97/2.01      inference(subtyping,[status(esa)],[c_12]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_12415,plain,
% 11.97/2.01      ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
% 11.97/2.01      | ~ l1_pre_topc(sK6)
% 11.97/2.01      | ~ v2_pre_topc(sK6) ),
% 11.97/2.01      inference(instantiation,[status(thm)],[c_2563]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_27,plain,
% 11.97/2.01      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 11.97/2.01      | ~ m1_pre_topc(X0,X1)
% 11.97/2.01      | ~ l1_pre_topc(X1) ),
% 11.97/2.01      inference(cnf_transformation,[],[f93]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_2555,plain,
% 11.97/2.01      ( r1_tarski(u1_struct_0(X0_59),u1_struct_0(X1_59))
% 11.97/2.01      | ~ m1_pre_topc(X0_59,X1_59)
% 11.97/2.01      | ~ l1_pre_topc(X1_59) ),
% 11.97/2.01      inference(subtyping,[status(esa)],[c_27]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_3947,plain,
% 11.97/2.01      ( r1_tarski(u1_struct_0(X0_59),u1_struct_0(sK7))
% 11.97/2.01      | ~ m1_pre_topc(X0_59,sK7)
% 11.97/2.01      | ~ l1_pre_topc(sK7) ),
% 11.97/2.01      inference(instantiation,[status(thm)],[c_2555]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_8168,plain,
% 11.97/2.01      ( r1_tarski(u1_struct_0(sK6),u1_struct_0(sK7))
% 11.97/2.01      | ~ m1_pre_topc(sK6,sK7)
% 11.97/2.01      | ~ l1_pre_topc(sK7) ),
% 11.97/2.01      inference(instantiation,[status(thm)],[c_3947]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_13,plain,
% 11.97/2.01      ( v3_pre_topc(X0,X1)
% 11.97/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.97/2.01      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 11.97/2.01      | ~ l1_pre_topc(X1) ),
% 11.97/2.01      inference(cnf_transformation,[],[f80]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_21,plain,
% 11.97/2.01      ( v1_tsep_1(X0,X1)
% 11.97/2.01      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 11.97/2.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.97/2.01      | ~ m1_pre_topc(X0,X1)
% 11.97/2.01      | ~ l1_pre_topc(X1)
% 11.97/2.01      | ~ v2_pre_topc(X1) ),
% 11.97/2.01      inference(cnf_transformation,[],[f117]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_25,plain,
% 11.97/2.01      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.97/2.01      | ~ m1_pre_topc(X0,X1)
% 11.97/2.01      | ~ l1_pre_topc(X1) ),
% 11.97/2.01      inference(cnf_transformation,[],[f91]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_267,plain,
% 11.97/2.01      ( ~ v3_pre_topc(u1_struct_0(X0),X1)
% 11.97/2.01      | v1_tsep_1(X0,X1)
% 11.97/2.01      | ~ m1_pre_topc(X0,X1)
% 11.97/2.01      | ~ l1_pre_topc(X1)
% 11.97/2.01      | ~ v2_pre_topc(X1) ),
% 11.97/2.01      inference(global_propositional_subsumption,
% 11.97/2.01                [status(thm)],
% 11.97/2.01                [c_21,c_25]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_268,plain,
% 11.97/2.01      ( v1_tsep_1(X0,X1)
% 11.97/2.01      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 11.97/2.01      | ~ m1_pre_topc(X0,X1)
% 11.97/2.01      | ~ l1_pre_topc(X1)
% 11.97/2.01      | ~ v2_pre_topc(X1) ),
% 11.97/2.01      inference(renaming,[status(thm)],[c_267]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_515,plain,
% 11.97/2.01      ( v1_tsep_1(X0,X1)
% 11.97/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 11.97/2.01      | ~ r2_hidden(X2,u1_pre_topc(X3))
% 11.97/2.01      | ~ m1_pre_topc(X0,X1)
% 11.97/2.01      | ~ l1_pre_topc(X3)
% 11.97/2.01      | ~ l1_pre_topc(X1)
% 11.97/2.01      | ~ v2_pre_topc(X1)
% 11.97/2.01      | X1 != X3
% 11.97/2.01      | u1_struct_0(X0) != X2 ),
% 11.97/2.01      inference(resolution_lifted,[status(thm)],[c_13,c_268]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_516,plain,
% 11.97/2.01      ( v1_tsep_1(X0,X1)
% 11.97/2.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.97/2.01      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
% 11.97/2.01      | ~ m1_pre_topc(X0,X1)
% 11.97/2.01      | ~ l1_pre_topc(X1)
% 11.97/2.01      | ~ v2_pre_topc(X1) ),
% 11.97/2.01      inference(unflattening,[status(thm)],[c_515]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_520,plain,
% 11.97/2.01      ( v1_tsep_1(X0,X1)
% 11.97/2.01      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
% 11.97/2.01      | ~ m1_pre_topc(X0,X1)
% 11.97/2.01      | ~ l1_pre_topc(X1)
% 11.97/2.01      | ~ v2_pre_topc(X1) ),
% 11.97/2.01      inference(global_propositional_subsumption,
% 11.97/2.01                [status(thm)],
% 11.97/2.01                [c_516,c_25]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_2535,plain,
% 11.97/2.01      ( v1_tsep_1(X0_59,X1_59)
% 11.97/2.01      | ~ r2_hidden(u1_struct_0(X0_59),u1_pre_topc(X1_59))
% 11.97/2.01      | ~ m1_pre_topc(X0_59,X1_59)
% 11.97/2.01      | ~ l1_pre_topc(X1_59)
% 11.97/2.01      | ~ v2_pre_topc(X1_59) ),
% 11.97/2.01      inference(subtyping,[status(esa)],[c_520]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_4637,plain,
% 11.97/2.01      ( v1_tsep_1(sK6,X0_59)
% 11.97/2.01      | ~ r2_hidden(u1_struct_0(sK6),u1_pre_topc(X0_59))
% 11.97/2.01      | ~ m1_pre_topc(sK6,X0_59)
% 11.97/2.01      | ~ l1_pre_topc(X0_59)
% 11.97/2.01      | ~ v2_pre_topc(X0_59) ),
% 11.97/2.01      inference(instantiation,[status(thm)],[c_2535]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_6889,plain,
% 11.97/2.01      ( v1_tsep_1(sK6,sK6)
% 11.97/2.01      | ~ r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
% 11.97/2.01      | ~ m1_pre_topc(sK6,sK6)
% 11.97/2.01      | ~ l1_pre_topc(sK6)
% 11.97/2.01      | ~ v2_pre_topc(sK6) ),
% 11.97/2.01      inference(instantiation,[status(thm)],[c_4637]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_26,plain,
% 11.97/2.01      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 11.97/2.01      inference(cnf_transformation,[],[f92]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_2556,plain,
% 11.97/2.01      ( m1_pre_topc(X0_59,X0_59) | ~ l1_pre_topc(X0_59) ),
% 11.97/2.01      inference(subtyping,[status(esa)],[c_26]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_3314,plain,
% 11.97/2.01      ( m1_pre_topc(X0_59,X0_59) = iProver_top
% 11.97/2.01      | l1_pre_topc(X0_59) != iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_2556]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_36,negated_conjecture,
% 11.97/2.01      ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
% 11.97/2.01      inference(cnf_transformation,[],[f110]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_2548,negated_conjecture,
% 11.97/2.01      ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
% 11.97/2.01      inference(subtyping,[status(esa)],[c_36]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_18,plain,
% 11.97/2.01      ( ~ m1_pre_topc(X0,X1)
% 11.97/2.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 11.97/2.01      | ~ l1_pre_topc(X0)
% 11.97/2.01      | ~ l1_pre_topc(X1) ),
% 11.97/2.01      inference(cnf_transformation,[],[f83]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_15,plain,
% 11.97/2.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 11.97/2.01      inference(cnf_transformation,[],[f81]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_275,plain,
% 11.97/2.01      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 11.97/2.01      | ~ m1_pre_topc(X0,X1)
% 11.97/2.01      | ~ l1_pre_topc(X1) ),
% 11.97/2.01      inference(global_propositional_subsumption,
% 11.97/2.01                [status(thm)],
% 11.97/2.01                [c_18,c_15]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_276,plain,
% 11.97/2.01      ( ~ m1_pre_topc(X0,X1)
% 11.97/2.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 11.97/2.01      | ~ l1_pre_topc(X1) ),
% 11.97/2.01      inference(renaming,[status(thm)],[c_275]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_2536,plain,
% 11.97/2.01      ( ~ m1_pre_topc(X0_59,X1_59)
% 11.97/2.01      | m1_pre_topc(X0_59,g1_pre_topc(u1_struct_0(X1_59),u1_pre_topc(X1_59)))
% 11.97/2.01      | ~ l1_pre_topc(X1_59) ),
% 11.97/2.01      inference(subtyping,[status(esa)],[c_276]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_3332,plain,
% 11.97/2.01      ( m1_pre_topc(X0_59,X1_59) != iProver_top
% 11.97/2.01      | m1_pre_topc(X0_59,g1_pre_topc(u1_struct_0(X1_59),u1_pre_topc(X1_59))) = iProver_top
% 11.97/2.01      | l1_pre_topc(X1_59) != iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_2536]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_6642,plain,
% 11.97/2.01      ( m1_pre_topc(X0_59,sK6) != iProver_top
% 11.97/2.01      | m1_pre_topc(X0_59,sK7) = iProver_top
% 11.97/2.01      | l1_pre_topc(sK6) != iProver_top ),
% 11.97/2.01      inference(superposition,[status(thm)],[c_2548,c_3332]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_47,negated_conjecture,
% 11.97/2.01      ( l1_pre_topc(sK4) ),
% 11.97/2.01      inference(cnf_transformation,[],[f99]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_52,plain,
% 11.97/2.01      ( l1_pre_topc(sK4) = iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_42,negated_conjecture,
% 11.97/2.01      ( m1_pre_topc(sK6,sK4) ),
% 11.97/2.01      inference(cnf_transformation,[],[f104]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_57,plain,
% 11.97/2.01      ( m1_pre_topc(sK6,sK4) = iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_2562,plain,
% 11.97/2.01      ( ~ m1_pre_topc(X0_59,X1_59)
% 11.97/2.01      | ~ l1_pre_topc(X1_59)
% 11.97/2.01      | l1_pre_topc(X0_59) ),
% 11.97/2.01      inference(subtyping,[status(esa)],[c_15]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_3745,plain,
% 11.97/2.01      ( ~ m1_pre_topc(sK6,X0_59)
% 11.97/2.01      | ~ l1_pre_topc(X0_59)
% 11.97/2.01      | l1_pre_topc(sK6) ),
% 11.97/2.01      inference(instantiation,[status(thm)],[c_2562]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_4491,plain,
% 11.97/2.01      ( ~ m1_pre_topc(sK6,sK4) | ~ l1_pre_topc(sK4) | l1_pre_topc(sK6) ),
% 11.97/2.01      inference(instantiation,[status(thm)],[c_3745]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_4492,plain,
% 11.97/2.01      ( m1_pre_topc(sK6,sK4) != iProver_top
% 11.97/2.01      | l1_pre_topc(sK4) != iProver_top
% 11.97/2.01      | l1_pre_topc(sK6) = iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_4491]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_6659,plain,
% 11.97/2.01      ( m1_pre_topc(X0_59,sK7) = iProver_top
% 11.97/2.01      | m1_pre_topc(X0_59,sK6) != iProver_top ),
% 11.97/2.01      inference(global_propositional_subsumption,
% 11.97/2.01                [status(thm)],
% 11.97/2.01                [c_6642,c_52,c_57,c_4492]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_6660,plain,
% 11.97/2.01      ( m1_pre_topc(X0_59,sK6) != iProver_top
% 11.97/2.01      | m1_pre_topc(X0_59,sK7) = iProver_top ),
% 11.97/2.01      inference(renaming,[status(thm)],[c_6659]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_6665,plain,
% 11.97/2.01      ( m1_pre_topc(sK6,sK7) = iProver_top
% 11.97/2.01      | l1_pre_topc(sK6) != iProver_top ),
% 11.97/2.01      inference(superposition,[status(thm)],[c_3314,c_6660]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_6669,plain,
% 11.97/2.01      ( m1_pre_topc(sK6,sK7) | ~ l1_pre_topc(sK6) ),
% 11.97/2.01      inference(predicate_to_equality_rev,[status(thm)],[c_6665]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_6203,plain,
% 11.97/2.01      ( m1_pre_topc(sK6,sK6) | ~ l1_pre_topc(sK6) ),
% 11.97/2.01      inference(instantiation,[status(thm)],[c_2556]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_16,plain,
% 11.97/2.01      ( m1_pre_topc(X0,X1)
% 11.97/2.01      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 11.97/2.01      | ~ l1_pre_topc(X1) ),
% 11.97/2.01      inference(cnf_transformation,[],[f82]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_2561,plain,
% 11.97/2.01      ( m1_pre_topc(X0_59,X1_59)
% 11.97/2.01      | ~ m1_pre_topc(X0_59,g1_pre_topc(u1_struct_0(X1_59),u1_pre_topc(X1_59)))
% 11.97/2.01      | ~ l1_pre_topc(X1_59) ),
% 11.97/2.01      inference(subtyping,[status(esa)],[c_16]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_3309,plain,
% 11.97/2.01      ( m1_pre_topc(X0_59,X1_59) = iProver_top
% 11.97/2.01      | m1_pre_topc(X0_59,g1_pre_topc(u1_struct_0(X1_59),u1_pre_topc(X1_59))) != iProver_top
% 11.97/2.01      | l1_pre_topc(X1_59) != iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_2561]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_5189,plain,
% 11.97/2.01      ( m1_pre_topc(X0_59,sK6) = iProver_top
% 11.97/2.01      | m1_pre_topc(X0_59,sK7) != iProver_top
% 11.97/2.01      | l1_pre_topc(sK6) != iProver_top ),
% 11.97/2.01      inference(superposition,[status(thm)],[c_2548,c_3309]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_5197,plain,
% 11.97/2.01      ( m1_pre_topc(X0_59,sK7) != iProver_top
% 11.97/2.01      | m1_pre_topc(X0_59,sK6) = iProver_top ),
% 11.97/2.01      inference(global_propositional_subsumption,
% 11.97/2.01                [status(thm)],
% 11.97/2.01                [c_5189,c_52,c_57,c_4492]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_5198,plain,
% 11.97/2.01      ( m1_pre_topc(X0_59,sK6) = iProver_top
% 11.97/2.01      | m1_pre_topc(X0_59,sK7) != iProver_top ),
% 11.97/2.01      inference(renaming,[status(thm)],[c_5197]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_5203,plain,
% 11.97/2.01      ( m1_pre_topc(sK7,sK6) = iProver_top
% 11.97/2.01      | l1_pre_topc(sK7) != iProver_top ),
% 11.97/2.01      inference(superposition,[status(thm)],[c_3314,c_5198]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_5204,plain,
% 11.97/2.01      ( m1_pre_topc(sK7,sK6) | ~ l1_pre_topc(sK7) ),
% 11.97/2.01      inference(predicate_to_equality_rev,[status(thm)],[c_5203]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_3869,plain,
% 11.97/2.01      ( ~ m1_pre_topc(sK7,X0_59)
% 11.97/2.01      | ~ l1_pre_topc(X0_59)
% 11.97/2.01      | l1_pre_topc(sK7) ),
% 11.97/2.01      inference(instantiation,[status(thm)],[c_2562]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_4645,plain,
% 11.97/2.01      ( ~ m1_pre_topc(sK7,sK4) | ~ l1_pre_topc(sK4) | l1_pre_topc(sK7) ),
% 11.97/2.01      inference(instantiation,[status(thm)],[c_3869]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_32,negated_conjecture,
% 11.97/2.01      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
% 11.97/2.01      inference(cnf_transformation,[],[f114]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_2552,negated_conjecture,
% 11.97/2.01      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
% 11.97/2.01      inference(subtyping,[status(esa)],[c_32]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_3318,plain,
% 11.97/2.01      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) = iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_2552]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_33,negated_conjecture,
% 11.97/2.01      ( sK9 = sK10 ),
% 11.97/2.01      inference(cnf_transformation,[],[f113]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_2551,negated_conjecture,
% 11.97/2.01      ( sK9 = sK10 ),
% 11.97/2.01      inference(subtyping,[status(esa)],[c_33]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_3338,plain,
% 11.97/2.01      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9) = iProver_top ),
% 11.97/2.01      inference(light_normalisation,[status(thm)],[c_3318,c_2551]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_29,plain,
% 11.97/2.01      ( r1_tmap_1(X0,X1,X2,X3)
% 11.97/2.01      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 11.97/2.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 11.97/2.01      | ~ v1_tsep_1(X4,X0)
% 11.97/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 11.97/2.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 11.97/2.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.97/2.01      | ~ m1_pre_topc(X4,X5)
% 11.97/2.01      | ~ m1_pre_topc(X0,X5)
% 11.97/2.01      | ~ m1_pre_topc(X4,X0)
% 11.97/2.01      | ~ v1_funct_1(X2)
% 11.97/2.01      | v2_struct_0(X5)
% 11.97/2.01      | v2_struct_0(X4)
% 11.97/2.01      | v2_struct_0(X0)
% 11.97/2.01      | v2_struct_0(X1)
% 11.97/2.01      | ~ l1_pre_topc(X5)
% 11.97/2.01      | ~ l1_pre_topc(X1)
% 11.97/2.01      | ~ v2_pre_topc(X5)
% 11.97/2.01      | ~ v2_pre_topc(X1) ),
% 11.97/2.01      inference(cnf_transformation,[],[f119]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_38,negated_conjecture,
% 11.97/2.01      ( v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
% 11.97/2.01      inference(cnf_transformation,[],[f108]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_650,plain,
% 11.97/2.01      ( r1_tmap_1(X0,X1,X2,X3)
% 11.97/2.01      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 11.97/2.01      | ~ v1_tsep_1(X4,X0)
% 11.97/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 11.97/2.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 11.97/2.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.97/2.01      | ~ m1_pre_topc(X4,X0)
% 11.97/2.01      | ~ m1_pre_topc(X4,X5)
% 11.97/2.01      | ~ m1_pre_topc(X0,X5)
% 11.97/2.01      | ~ v1_funct_1(X2)
% 11.97/2.01      | v2_struct_0(X1)
% 11.97/2.01      | v2_struct_0(X4)
% 11.97/2.01      | v2_struct_0(X0)
% 11.97/2.01      | v2_struct_0(X5)
% 11.97/2.01      | ~ l1_pre_topc(X1)
% 11.97/2.01      | ~ l1_pre_topc(X5)
% 11.97/2.01      | ~ v2_pre_topc(X1)
% 11.97/2.01      | ~ v2_pre_topc(X5)
% 11.97/2.01      | u1_struct_0(X1) != u1_struct_0(sK5)
% 11.97/2.01      | u1_struct_0(X0) != u1_struct_0(sK7)
% 11.97/2.01      | sK8 != X2 ),
% 11.97/2.01      inference(resolution_lifted,[status(thm)],[c_29,c_38]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_651,plain,
% 11.97/2.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 11.97/2.01      | r1_tmap_1(X3,X1,sK8,X4)
% 11.97/2.01      | ~ v1_tsep_1(X0,X3)
% 11.97/2.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 11.97/2.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 11.97/2.01      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 11.97/2.01      | ~ m1_pre_topc(X0,X3)
% 11.97/2.01      | ~ m1_pre_topc(X0,X2)
% 11.97/2.01      | ~ m1_pre_topc(X3,X2)
% 11.97/2.01      | ~ v1_funct_1(sK8)
% 11.97/2.01      | v2_struct_0(X1)
% 11.97/2.01      | v2_struct_0(X0)
% 11.97/2.01      | v2_struct_0(X3)
% 11.97/2.01      | v2_struct_0(X2)
% 11.97/2.01      | ~ l1_pre_topc(X1)
% 11.97/2.01      | ~ l1_pre_topc(X2)
% 11.97/2.01      | ~ v2_pre_topc(X1)
% 11.97/2.01      | ~ v2_pre_topc(X2)
% 11.97/2.01      | u1_struct_0(X1) != u1_struct_0(sK5)
% 11.97/2.01      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 11.97/2.01      inference(unflattening,[status(thm)],[c_650]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_39,negated_conjecture,
% 11.97/2.01      ( v1_funct_1(sK8) ),
% 11.97/2.01      inference(cnf_transformation,[],[f107]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_655,plain,
% 11.97/2.01      ( ~ m1_pre_topc(X3,X2)
% 11.97/2.01      | ~ m1_pre_topc(X0,X2)
% 11.97/2.01      | ~ m1_pre_topc(X0,X3)
% 11.97/2.01      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 11.97/2.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 11.97/2.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 11.97/2.01      | ~ v1_tsep_1(X0,X3)
% 11.97/2.01      | r1_tmap_1(X3,X1,sK8,X4)
% 11.97/2.01      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 11.97/2.01      | v2_struct_0(X1)
% 11.97/2.01      | v2_struct_0(X0)
% 11.97/2.01      | v2_struct_0(X3)
% 11.97/2.01      | v2_struct_0(X2)
% 11.97/2.01      | ~ l1_pre_topc(X1)
% 11.97/2.01      | ~ l1_pre_topc(X2)
% 11.97/2.01      | ~ v2_pre_topc(X1)
% 11.97/2.01      | ~ v2_pre_topc(X2)
% 11.97/2.01      | u1_struct_0(X1) != u1_struct_0(sK5)
% 11.97/2.01      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 11.97/2.01      inference(global_propositional_subsumption,
% 11.97/2.01                [status(thm)],
% 11.97/2.01                [c_651,c_39]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_656,plain,
% 11.97/2.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 11.97/2.01      | r1_tmap_1(X3,X1,sK8,X4)
% 11.97/2.01      | ~ v1_tsep_1(X0,X3)
% 11.97/2.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 11.97/2.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 11.97/2.01      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 11.97/2.01      | ~ m1_pre_topc(X0,X2)
% 11.97/2.01      | ~ m1_pre_topc(X0,X3)
% 11.97/2.01      | ~ m1_pre_topc(X3,X2)
% 11.97/2.01      | v2_struct_0(X1)
% 11.97/2.01      | v2_struct_0(X2)
% 11.97/2.01      | v2_struct_0(X0)
% 11.97/2.01      | v2_struct_0(X3)
% 11.97/2.01      | ~ l1_pre_topc(X1)
% 11.97/2.01      | ~ l1_pre_topc(X2)
% 11.97/2.01      | ~ v2_pre_topc(X1)
% 11.97/2.01      | ~ v2_pre_topc(X2)
% 11.97/2.01      | u1_struct_0(X1) != u1_struct_0(sK5)
% 11.97/2.01      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 11.97/2.01      inference(renaming,[status(thm)],[c_655]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_28,plain,
% 11.97/2.01      ( ~ m1_pre_topc(X0,X1)
% 11.97/2.01      | ~ m1_pre_topc(X2,X0)
% 11.97/2.01      | m1_pre_topc(X2,X1)
% 11.97/2.01      | ~ l1_pre_topc(X1)
% 11.97/2.01      | ~ v2_pre_topc(X1) ),
% 11.97/2.01      inference(cnf_transformation,[],[f94]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_699,plain,
% 11.97/2.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 11.97/2.01      | r1_tmap_1(X3,X1,sK8,X4)
% 11.97/2.01      | ~ v1_tsep_1(X0,X3)
% 11.97/2.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 11.97/2.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 11.97/2.01      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 11.97/2.01      | ~ m1_pre_topc(X0,X3)
% 11.97/2.01      | ~ m1_pre_topc(X3,X2)
% 11.97/2.01      | v2_struct_0(X1)
% 11.97/2.01      | v2_struct_0(X2)
% 11.97/2.01      | v2_struct_0(X0)
% 11.97/2.01      | v2_struct_0(X3)
% 11.97/2.01      | ~ l1_pre_topc(X1)
% 11.97/2.01      | ~ l1_pre_topc(X2)
% 11.97/2.01      | ~ v2_pre_topc(X1)
% 11.97/2.01      | ~ v2_pre_topc(X2)
% 11.97/2.01      | u1_struct_0(X1) != u1_struct_0(sK5)
% 11.97/2.01      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 11.97/2.01      inference(forward_subsumption_resolution,
% 11.97/2.01                [status(thm)],
% 11.97/2.01                [c_656,c_28]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_2532,plain,
% 11.97/2.01      ( ~ r1_tmap_1(X0_59,X1_59,k3_tmap_1(X2_59,X1_59,X3_59,X0_59,sK8),X0_60)
% 11.97/2.01      | r1_tmap_1(X3_59,X1_59,sK8,X0_60)
% 11.97/2.01      | ~ v1_tsep_1(X0_59,X3_59)
% 11.97/2.01      | ~ m1_subset_1(X0_60,u1_struct_0(X0_59))
% 11.97/2.01      | ~ m1_subset_1(X0_60,u1_struct_0(X3_59))
% 11.97/2.01      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_59),u1_struct_0(X1_59))))
% 11.97/2.01      | ~ m1_pre_topc(X0_59,X3_59)
% 11.97/2.01      | ~ m1_pre_topc(X3_59,X2_59)
% 11.97/2.01      | v2_struct_0(X1_59)
% 11.97/2.01      | v2_struct_0(X2_59)
% 11.97/2.01      | v2_struct_0(X0_59)
% 11.97/2.01      | v2_struct_0(X3_59)
% 11.97/2.01      | ~ l1_pre_topc(X1_59)
% 11.97/2.01      | ~ l1_pre_topc(X2_59)
% 11.97/2.01      | ~ v2_pre_topc(X1_59)
% 11.97/2.01      | ~ v2_pre_topc(X2_59)
% 11.97/2.01      | u1_struct_0(X1_59) != u1_struct_0(sK5)
% 11.97/2.01      | u1_struct_0(X3_59) != u1_struct_0(sK7) ),
% 11.97/2.01      inference(subtyping,[status(esa)],[c_699]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_3336,plain,
% 11.97/2.01      ( u1_struct_0(X0_59) != u1_struct_0(sK5)
% 11.97/2.01      | u1_struct_0(X1_59) != u1_struct_0(sK7)
% 11.97/2.01      | r1_tmap_1(X2_59,X0_59,k3_tmap_1(X3_59,X0_59,X1_59,X2_59,sK8),X0_60) != iProver_top
% 11.97/2.01      | r1_tmap_1(X1_59,X0_59,sK8,X0_60) = iProver_top
% 11.97/2.01      | v1_tsep_1(X2_59,X1_59) != iProver_top
% 11.97/2.01      | m1_subset_1(X0_60,u1_struct_0(X2_59)) != iProver_top
% 11.97/2.01      | m1_subset_1(X0_60,u1_struct_0(X1_59)) != iProver_top
% 11.97/2.01      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_59),u1_struct_0(X0_59)))) != iProver_top
% 11.97/2.01      | m1_pre_topc(X2_59,X1_59) != iProver_top
% 11.97/2.01      | m1_pre_topc(X1_59,X3_59) != iProver_top
% 11.97/2.01      | v2_struct_0(X2_59) = iProver_top
% 11.97/2.01      | v2_struct_0(X0_59) = iProver_top
% 11.97/2.01      | v2_struct_0(X3_59) = iProver_top
% 11.97/2.01      | v2_struct_0(X1_59) = iProver_top
% 11.97/2.01      | l1_pre_topc(X0_59) != iProver_top
% 11.97/2.01      | l1_pre_topc(X3_59) != iProver_top
% 11.97/2.01      | v2_pre_topc(X0_59) != iProver_top
% 11.97/2.01      | v2_pre_topc(X3_59) != iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_2532]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_4439,plain,
% 11.97/2.01      ( u1_struct_0(X0_59) != u1_struct_0(sK7)
% 11.97/2.01      | r1_tmap_1(X1_59,sK5,k3_tmap_1(X2_59,sK5,X0_59,X1_59,sK8),X0_60) != iProver_top
% 11.97/2.01      | r1_tmap_1(X0_59,sK5,sK8,X0_60) = iProver_top
% 11.97/2.01      | v1_tsep_1(X1_59,X0_59) != iProver_top
% 11.97/2.01      | m1_subset_1(X0_60,u1_struct_0(X0_59)) != iProver_top
% 11.97/2.01      | m1_subset_1(X0_60,u1_struct_0(X1_59)) != iProver_top
% 11.97/2.01      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(sK5)))) != iProver_top
% 11.97/2.01      | m1_pre_topc(X0_59,X2_59) != iProver_top
% 11.97/2.01      | m1_pre_topc(X1_59,X0_59) != iProver_top
% 11.97/2.01      | v2_struct_0(X0_59) = iProver_top
% 11.97/2.01      | v2_struct_0(X1_59) = iProver_top
% 11.97/2.01      | v2_struct_0(X2_59) = iProver_top
% 11.97/2.01      | v2_struct_0(sK5) = iProver_top
% 11.97/2.01      | l1_pre_topc(X2_59) != iProver_top
% 11.97/2.01      | l1_pre_topc(sK5) != iProver_top
% 11.97/2.01      | v2_pre_topc(X2_59) != iProver_top
% 11.97/2.01      | v2_pre_topc(sK5) != iProver_top ),
% 11.97/2.01      inference(equality_resolution,[status(thm)],[c_3336]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_46,negated_conjecture,
% 11.97/2.01      ( ~ v2_struct_0(sK5) ),
% 11.97/2.01      inference(cnf_transformation,[],[f100]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_53,plain,
% 11.97/2.01      ( v2_struct_0(sK5) != iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_45,negated_conjecture,
% 11.97/2.01      ( v2_pre_topc(sK5) ),
% 11.97/2.01      inference(cnf_transformation,[],[f101]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_54,plain,
% 11.97/2.01      ( v2_pre_topc(sK5) = iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_44,negated_conjecture,
% 11.97/2.01      ( l1_pre_topc(sK5) ),
% 11.97/2.01      inference(cnf_transformation,[],[f102]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_55,plain,
% 11.97/2.01      ( l1_pre_topc(sK5) = iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_4516,plain,
% 11.97/2.01      ( v2_pre_topc(X2_59) != iProver_top
% 11.97/2.01      | v2_struct_0(X2_59) = iProver_top
% 11.97/2.01      | v2_struct_0(X1_59) = iProver_top
% 11.97/2.01      | v2_struct_0(X0_59) = iProver_top
% 11.97/2.01      | m1_pre_topc(X1_59,X0_59) != iProver_top
% 11.97/2.01      | m1_pre_topc(X0_59,X2_59) != iProver_top
% 11.97/2.01      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(sK5)))) != iProver_top
% 11.97/2.01      | m1_subset_1(X0_60,u1_struct_0(X1_59)) != iProver_top
% 11.97/2.01      | m1_subset_1(X0_60,u1_struct_0(X0_59)) != iProver_top
% 11.97/2.01      | v1_tsep_1(X1_59,X0_59) != iProver_top
% 11.97/2.01      | r1_tmap_1(X0_59,sK5,sK8,X0_60) = iProver_top
% 11.97/2.01      | r1_tmap_1(X1_59,sK5,k3_tmap_1(X2_59,sK5,X0_59,X1_59,sK8),X0_60) != iProver_top
% 11.97/2.01      | u1_struct_0(X0_59) != u1_struct_0(sK7)
% 11.97/2.01      | l1_pre_topc(X2_59) != iProver_top ),
% 11.97/2.01      inference(global_propositional_subsumption,
% 11.97/2.01                [status(thm)],
% 11.97/2.01                [c_4439,c_53,c_54,c_55]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_4517,plain,
% 11.97/2.01      ( u1_struct_0(X0_59) != u1_struct_0(sK7)
% 11.97/2.01      | r1_tmap_1(X1_59,sK5,k3_tmap_1(X2_59,sK5,X0_59,X1_59,sK8),X0_60) != iProver_top
% 11.97/2.01      | r1_tmap_1(X0_59,sK5,sK8,X0_60) = iProver_top
% 11.97/2.01      | v1_tsep_1(X1_59,X0_59) != iProver_top
% 11.97/2.01      | m1_subset_1(X0_60,u1_struct_0(X0_59)) != iProver_top
% 11.97/2.01      | m1_subset_1(X0_60,u1_struct_0(X1_59)) != iProver_top
% 11.97/2.01      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(sK5)))) != iProver_top
% 11.97/2.01      | m1_pre_topc(X0_59,X2_59) != iProver_top
% 11.97/2.01      | m1_pre_topc(X1_59,X0_59) != iProver_top
% 11.97/2.01      | v2_struct_0(X0_59) = iProver_top
% 11.97/2.01      | v2_struct_0(X1_59) = iProver_top
% 11.97/2.01      | v2_struct_0(X2_59) = iProver_top
% 11.97/2.01      | l1_pre_topc(X2_59) != iProver_top
% 11.97/2.01      | v2_pre_topc(X2_59) != iProver_top ),
% 11.97/2.01      inference(renaming,[status(thm)],[c_4516]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_4520,plain,
% 11.97/2.01      ( r1_tmap_1(X0_59,sK5,k3_tmap_1(X1_59,sK5,sK7,X0_59,sK8),X0_60) != iProver_top
% 11.97/2.01      | r1_tmap_1(sK7,sK5,sK8,X0_60) = iProver_top
% 11.97/2.01      | v1_tsep_1(X0_59,sK7) != iProver_top
% 11.97/2.01      | m1_subset_1(X0_60,u1_struct_0(X0_59)) != iProver_top
% 11.97/2.01      | m1_subset_1(X0_60,u1_struct_0(sK7)) != iProver_top
% 11.97/2.01      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
% 11.97/2.01      | m1_pre_topc(X0_59,sK7) != iProver_top
% 11.97/2.01      | m1_pre_topc(sK7,X1_59) != iProver_top
% 11.97/2.01      | v2_struct_0(X0_59) = iProver_top
% 11.97/2.01      | v2_struct_0(X1_59) = iProver_top
% 11.97/2.01      | v2_struct_0(sK7) = iProver_top
% 11.97/2.01      | l1_pre_topc(X1_59) != iProver_top
% 11.97/2.01      | v2_pre_topc(X1_59) != iProver_top ),
% 11.97/2.01      inference(equality_resolution,[status(thm)],[c_4517]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_41,negated_conjecture,
% 11.97/2.01      ( ~ v2_struct_0(sK7) ),
% 11.97/2.01      inference(cnf_transformation,[],[f105]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_58,plain,
% 11.97/2.01      ( v2_struct_0(sK7) != iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_37,negated_conjecture,
% 11.97/2.01      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
% 11.97/2.01      inference(cnf_transformation,[],[f109]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_62,plain,
% 11.97/2.01      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) = iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_4613,plain,
% 11.97/2.01      ( v2_struct_0(X1_59) = iProver_top
% 11.97/2.01      | v2_struct_0(X0_59) = iProver_top
% 11.97/2.01      | m1_pre_topc(sK7,X1_59) != iProver_top
% 11.97/2.01      | m1_pre_topc(X0_59,sK7) != iProver_top
% 11.97/2.01      | r1_tmap_1(X0_59,sK5,k3_tmap_1(X1_59,sK5,sK7,X0_59,sK8),X0_60) != iProver_top
% 11.97/2.01      | r1_tmap_1(sK7,sK5,sK8,X0_60) = iProver_top
% 11.97/2.01      | v1_tsep_1(X0_59,sK7) != iProver_top
% 11.97/2.01      | m1_subset_1(X0_60,u1_struct_0(X0_59)) != iProver_top
% 11.97/2.01      | m1_subset_1(X0_60,u1_struct_0(sK7)) != iProver_top
% 11.97/2.01      | l1_pre_topc(X1_59) != iProver_top
% 11.97/2.01      | v2_pre_topc(X1_59) != iProver_top ),
% 11.97/2.01      inference(global_propositional_subsumption,
% 11.97/2.01                [status(thm)],
% 11.97/2.01                [c_4520,c_58,c_62]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_4614,plain,
% 11.97/2.01      ( r1_tmap_1(X0_59,sK5,k3_tmap_1(X1_59,sK5,sK7,X0_59,sK8),X0_60) != iProver_top
% 11.97/2.01      | r1_tmap_1(sK7,sK5,sK8,X0_60) = iProver_top
% 11.97/2.01      | v1_tsep_1(X0_59,sK7) != iProver_top
% 11.97/2.01      | m1_subset_1(X0_60,u1_struct_0(X0_59)) != iProver_top
% 11.97/2.01      | m1_subset_1(X0_60,u1_struct_0(sK7)) != iProver_top
% 11.97/2.01      | m1_pre_topc(X0_59,sK7) != iProver_top
% 11.97/2.01      | m1_pre_topc(sK7,X1_59) != iProver_top
% 11.97/2.01      | v2_struct_0(X0_59) = iProver_top
% 11.97/2.01      | v2_struct_0(X1_59) = iProver_top
% 11.97/2.01      | l1_pre_topc(X1_59) != iProver_top
% 11.97/2.01      | v2_pre_topc(X1_59) != iProver_top ),
% 11.97/2.01      inference(renaming,[status(thm)],[c_4613]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_4619,plain,
% 11.97/2.01      ( r1_tmap_1(sK7,sK5,sK8,sK9) = iProver_top
% 11.97/2.01      | v1_tsep_1(sK6,sK7) != iProver_top
% 11.97/2.01      | m1_subset_1(sK9,u1_struct_0(sK6)) != iProver_top
% 11.97/2.01      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 11.97/2.01      | m1_pre_topc(sK6,sK7) != iProver_top
% 11.97/2.01      | m1_pre_topc(sK7,sK4) != iProver_top
% 11.97/2.01      | v2_struct_0(sK4) = iProver_top
% 11.97/2.01      | v2_struct_0(sK6) = iProver_top
% 11.97/2.01      | l1_pre_topc(sK4) != iProver_top
% 11.97/2.01      | v2_pre_topc(sK4) != iProver_top ),
% 11.97/2.01      inference(superposition,[status(thm)],[c_3338,c_4614]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_49,negated_conjecture,
% 11.97/2.01      ( ~ v2_struct_0(sK4) ),
% 11.97/2.01      inference(cnf_transformation,[],[f97]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_50,plain,
% 11.97/2.01      ( v2_struct_0(sK4) != iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_48,negated_conjecture,
% 11.97/2.01      ( v2_pre_topc(sK4) ),
% 11.97/2.01      inference(cnf_transformation,[],[f98]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_51,plain,
% 11.97/2.01      ( v2_pre_topc(sK4) = iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_43,negated_conjecture,
% 11.97/2.01      ( ~ v2_struct_0(sK6) ),
% 11.97/2.01      inference(cnf_transformation,[],[f103]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_56,plain,
% 11.97/2.01      ( v2_struct_0(sK6) != iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_40,negated_conjecture,
% 11.97/2.01      ( m1_pre_topc(sK7,sK4) ),
% 11.97/2.01      inference(cnf_transformation,[],[f106]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_59,plain,
% 11.97/2.01      ( m1_pre_topc(sK7,sK4) = iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_35,negated_conjecture,
% 11.97/2.01      ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
% 11.97/2.01      inference(cnf_transformation,[],[f111]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_63,plain,
% 11.97/2.01      ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_31,negated_conjecture,
% 11.97/2.01      ( ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
% 11.97/2.01      inference(cnf_transformation,[],[f115]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_66,plain,
% 11.97/2.01      ( r1_tmap_1(sK7,sK5,sK8,sK9) != iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_34,negated_conjecture,
% 11.97/2.01      ( m1_subset_1(sK10,u1_struct_0(sK6)) ),
% 11.97/2.01      inference(cnf_transformation,[],[f112]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_2550,negated_conjecture,
% 11.97/2.01      ( m1_subset_1(sK10,u1_struct_0(sK6)) ),
% 11.97/2.01      inference(subtyping,[status(esa)],[c_34]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_3319,plain,
% 11.97/2.01      ( m1_subset_1(sK10,u1_struct_0(sK6)) = iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_2550]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_3337,plain,
% 11.97/2.01      ( m1_subset_1(sK9,u1_struct_0(sK6)) = iProver_top ),
% 11.97/2.01      inference(light_normalisation,[status(thm)],[c_3319,c_2551]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_4623,plain,
% 11.97/2.01      ( m1_pre_topc(sK6,sK7) != iProver_top
% 11.97/2.01      | v1_tsep_1(sK6,sK7) != iProver_top ),
% 11.97/2.01      inference(global_propositional_subsumption,
% 11.97/2.01                [status(thm)],
% 11.97/2.01                [c_4619,c_50,c_51,c_52,c_56,c_59,c_63,c_66,c_3337]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_4624,plain,
% 11.97/2.01      ( v1_tsep_1(sK6,sK7) != iProver_top
% 11.97/2.01      | m1_pre_topc(sK6,sK7) != iProver_top ),
% 11.97/2.01      inference(renaming,[status(thm)],[c_4623]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_4625,plain,
% 11.97/2.01      ( ~ v1_tsep_1(sK6,sK7) | ~ m1_pre_topc(sK6,sK7) ),
% 11.97/2.01      inference(predicate_to_equality_rev,[status(thm)],[c_4624]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_2544,negated_conjecture,
% 11.97/2.01      ( m1_pre_topc(sK6,sK4) ),
% 11.97/2.01      inference(subtyping,[status(esa)],[c_42]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_3324,plain,
% 11.97/2.01      ( m1_pre_topc(sK6,sK4) = iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_2544]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_0,plain,
% 11.97/2.01      ( ~ m1_pre_topc(X0,X1)
% 11.97/2.01      | ~ l1_pre_topc(X1)
% 11.97/2.01      | ~ v2_pre_topc(X1)
% 11.97/2.01      | v2_pre_topc(X0) ),
% 11.97/2.01      inference(cnf_transformation,[],[f66]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_2575,plain,
% 11.97/2.01      ( ~ m1_pre_topc(X0_59,X1_59)
% 11.97/2.01      | ~ l1_pre_topc(X1_59)
% 11.97/2.01      | ~ v2_pre_topc(X1_59)
% 11.97/2.01      | v2_pre_topc(X0_59) ),
% 11.97/2.01      inference(subtyping,[status(esa)],[c_0]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_3295,plain,
% 11.97/2.01      ( m1_pre_topc(X0_59,X1_59) != iProver_top
% 11.97/2.01      | l1_pre_topc(X1_59) != iProver_top
% 11.97/2.01      | v2_pre_topc(X1_59) != iProver_top
% 11.97/2.01      | v2_pre_topc(X0_59) = iProver_top ),
% 11.97/2.01      inference(predicate_to_equality,[status(thm)],[c_2575]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_3649,plain,
% 11.97/2.01      ( l1_pre_topc(sK4) != iProver_top
% 11.97/2.01      | v2_pre_topc(sK4) != iProver_top
% 11.97/2.01      | v2_pre_topc(sK6) = iProver_top ),
% 11.97/2.01      inference(superposition,[status(thm)],[c_3324,c_3295]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(c_3650,plain,
% 11.97/2.01      ( ~ l1_pre_topc(sK4) | ~ v2_pre_topc(sK4) | v2_pre_topc(sK6) ),
% 11.97/2.01      inference(predicate_to_equality_rev,[status(thm)],[c_3649]) ).
% 11.97/2.01  
% 11.97/2.01  cnf(contradiction,plain,
% 11.97/2.01      ( $false ),
% 11.97/2.01      inference(minisat,
% 11.97/2.01                [status(thm)],
% 11.97/2.01                [c_30209,c_12415,c_8168,c_6889,c_6669,c_6203,c_5204,
% 11.97/2.01                 c_4645,c_4625,c_4491,c_3650,c_40,c_41,c_42,c_43,c_47,
% 11.97/2.01                 c_48]) ).
% 11.97/2.01  
% 11.97/2.01  
% 11.97/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.97/2.01  
% 11.97/2.01  ------                               Statistics
% 11.97/2.01  
% 11.97/2.01  ------ General
% 11.97/2.01  
% 11.97/2.01  abstr_ref_over_cycles:                  0
% 11.97/2.01  abstr_ref_under_cycles:                 0
% 11.97/2.01  gc_basic_clause_elim:                   0
% 11.97/2.01  forced_gc_time:                         0
% 11.97/2.01  parsing_time:                           0.014
% 11.97/2.01  unif_index_cands_time:                  0.
% 11.97/2.01  unif_index_add_time:                    0.
% 11.97/2.01  orderings_time:                         0.
% 11.97/2.01  out_proof_time:                         0.016
% 11.97/2.01  total_time:                             1.482
% 11.97/2.01  num_of_symbols:                         64
% 11.97/2.01  num_of_terms:                           8922
% 11.97/2.01  
% 11.97/2.01  ------ Preprocessing
% 11.97/2.01  
% 11.97/2.01  num_of_splits:                          0
% 11.97/2.01  num_of_split_atoms:                     0
% 11.97/2.01  num_of_reused_defs:                     0
% 11.97/2.01  num_eq_ax_congr_red:                    19
% 11.97/2.01  num_of_sem_filtered_clauses:            1
% 11.97/2.01  num_of_subtypes:                        2
% 11.97/2.01  monotx_restored_types:                  0
% 11.97/2.01  sat_num_of_epr_types:                   0
% 11.97/2.01  sat_num_of_non_cyclic_types:            0
% 11.97/2.01  sat_guarded_non_collapsed_types:        0
% 11.97/2.01  num_pure_diseq_elim:                    0
% 11.97/2.01  simp_replaced_by:                       0
% 11.97/2.01  res_preprocessed:                       221
% 11.97/2.01  prep_upred:                             0
% 11.97/2.01  prep_unflattend:                        22
% 11.97/2.01  smt_new_axioms:                         0
% 11.97/2.01  pred_elim_cands:                        10
% 11.97/2.01  pred_elim:                              3
% 11.97/2.01  pred_elim_cl:                           4
% 11.97/2.01  pred_elim_cycles:                       7
% 11.97/2.01  merged_defs:                            0
% 11.97/2.01  merged_defs_ncl:                        0
% 11.97/2.01  bin_hyper_res:                          0
% 11.97/2.01  prep_cycles:                            4
% 11.97/2.01  pred_elim_time:                         0.038
% 11.97/2.01  splitting_time:                         0.
% 11.97/2.01  sem_filter_time:                        0.
% 11.97/2.01  monotx_time:                            0.
% 11.97/2.01  subtype_inf_time:                       0.001
% 11.97/2.01  
% 11.97/2.01  ------ Problem properties
% 11.97/2.01  
% 11.97/2.01  clauses:                                44
% 11.97/2.01  conjectures:                            17
% 11.97/2.01  epr:                                    17
% 11.97/2.01  horn:                                   34
% 11.97/2.01  ground:                                 17
% 11.97/2.01  unary:                                  17
% 11.97/2.01  binary:                                 6
% 11.97/2.01  lits:                                   152
% 11.97/2.01  lits_eq:                                6
% 11.97/2.01  fd_pure:                                0
% 11.97/2.01  fd_pseudo:                              0
% 11.97/2.01  fd_cond:                                0
% 11.97/2.01  fd_pseudo_cond:                         0
% 11.97/2.01  ac_symbols:                             0
% 11.97/2.01  
% 11.97/2.01  ------ Propositional Solver
% 11.97/2.01  
% 11.97/2.01  prop_solver_calls:                      34
% 11.97/2.01  prop_fast_solver_calls:                 3652
% 11.97/2.01  smt_solver_calls:                       0
% 11.97/2.01  smt_fast_solver_calls:                  0
% 11.97/2.01  prop_num_of_clauses:                    12667
% 11.97/2.01  prop_preprocess_simplified:             16232
% 11.97/2.01  prop_fo_subsumed:                       324
% 11.97/2.01  prop_solver_time:                       0.
% 11.97/2.01  smt_solver_time:                        0.
% 11.97/2.01  smt_fast_solver_time:                   0.
% 11.97/2.01  prop_fast_solver_time:                  0.
% 11.97/2.01  prop_unsat_core_time:                   0.001
% 11.97/2.01  
% 11.97/2.01  ------ QBF
% 11.97/2.01  
% 11.97/2.01  qbf_q_res:                              0
% 11.97/2.01  qbf_num_tautologies:                    0
% 11.97/2.01  qbf_prep_cycles:                        0
% 11.97/2.01  
% 11.97/2.01  ------ BMC1
% 11.97/2.01  
% 11.97/2.01  bmc1_current_bound:                     -1
% 11.97/2.01  bmc1_last_solved_bound:                 -1
% 11.97/2.01  bmc1_unsat_core_size:                   -1
% 11.97/2.01  bmc1_unsat_core_parents_size:           -1
% 11.97/2.01  bmc1_merge_next_fun:                    0
% 11.97/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.97/2.01  
% 11.97/2.01  ------ Instantiation
% 11.97/2.01  
% 11.97/2.01  inst_num_of_clauses:                    2171
% 11.97/2.01  inst_num_in_passive:                    7
% 11.97/2.01  inst_num_in_active:                     1349
% 11.97/2.01  inst_num_in_unprocessed:                814
% 11.97/2.01  inst_num_of_loops:                      1456
% 11.97/2.01  inst_num_of_learning_restarts:          0
% 11.97/2.01  inst_num_moves_active_passive:          99
% 11.97/2.01  inst_lit_activity:                      0
% 11.97/2.01  inst_lit_activity_moves:                0
% 11.97/2.01  inst_num_tautologies:                   0
% 11.97/2.01  inst_num_prop_implied:                  0
% 11.97/2.01  inst_num_existing_simplified:           0
% 11.97/2.01  inst_num_eq_res_simplified:             0
% 11.97/2.01  inst_num_child_elim:                    0
% 11.97/2.01  inst_num_of_dismatching_blockings:      1429
% 11.97/2.01  inst_num_of_non_proper_insts:           4843
% 11.97/2.01  inst_num_of_duplicates:                 0
% 11.97/2.01  inst_inst_num_from_inst_to_res:         0
% 11.97/2.01  inst_dismatching_checking_time:         0.
% 11.97/2.01  
% 11.97/2.01  ------ Resolution
% 11.97/2.01  
% 11.97/2.01  res_num_of_clauses:                     0
% 11.97/2.01  res_num_in_passive:                     0
% 11.97/2.01  res_num_in_active:                      0
% 11.97/2.01  res_num_of_loops:                       225
% 11.97/2.01  res_forward_subset_subsumed:            442
% 11.97/2.01  res_backward_subset_subsumed:           2
% 11.97/2.01  res_forward_subsumed:                   0
% 11.97/2.01  res_backward_subsumed:                  0
% 11.97/2.01  res_forward_subsumption_resolution:     2
% 11.97/2.01  res_backward_subsumption_resolution:    0
% 11.97/2.01  res_clause_to_clause_subsumption:       33030
% 11.97/2.01  res_orphan_elimination:                 0
% 11.97/2.01  res_tautology_del:                      719
% 11.97/2.01  res_num_eq_res_simplified:              0
% 11.97/2.01  res_num_sel_changes:                    0
% 11.97/2.01  res_moves_from_active_to_pass:          0
% 11.97/2.01  
% 11.97/2.01  ------ Superposition
% 11.97/2.01  
% 11.97/2.01  sup_time_total:                         0.
% 11.97/2.01  sup_time_generating:                    0.
% 11.97/2.01  sup_time_sim_full:                      0.
% 11.97/2.01  sup_time_sim_immed:                     0.
% 11.97/2.01  
% 11.97/2.01  sup_num_of_clauses:                     1488
% 11.97/2.01  sup_num_in_active:                      287
% 11.97/2.01  sup_num_in_passive:                     1201
% 11.97/2.01  sup_num_of_loops:                       290
% 11.97/2.01  sup_fw_superposition:                   2915
% 11.97/2.01  sup_bw_superposition:                   2328
% 11.97/2.01  sup_immediate_simplified:               1545
% 11.97/2.01  sup_given_eliminated:                   2
% 11.97/2.01  comparisons_done:                       0
% 11.97/2.01  comparisons_avoided:                    0
% 11.97/2.01  
% 11.97/2.01  ------ Simplifications
% 11.97/2.01  
% 11.97/2.01  
% 11.97/2.01  sim_fw_subset_subsumed:                 897
% 11.97/2.01  sim_bw_subset_subsumed:                 214
% 11.97/2.01  sim_fw_subsumed:                        563
% 11.97/2.01  sim_bw_subsumed:                        35
% 11.97/2.01  sim_fw_subsumption_res:                 0
% 11.97/2.01  sim_bw_subsumption_res:                 0
% 11.97/2.01  sim_tautology_del:                      62
% 11.97/2.01  sim_eq_tautology_del:                   0
% 11.97/2.01  sim_eq_res_simp:                        0
% 11.97/2.01  sim_fw_demodulated:                     0
% 11.97/2.01  sim_bw_demodulated:                     0
% 11.97/2.01  sim_light_normalised:                   88
% 11.97/2.01  sim_joinable_taut:                      0
% 11.97/2.01  sim_joinable_simp:                      0
% 11.97/2.01  sim_ac_normalised:                      0
% 11.97/2.01  sim_smt_subsumption:                    0
% 11.97/2.01  
%------------------------------------------------------------------------------
