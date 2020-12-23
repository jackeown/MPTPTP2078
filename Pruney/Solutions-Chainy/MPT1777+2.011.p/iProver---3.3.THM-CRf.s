%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:26 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 697 expanded)
%              Number of clauses        :  105 ( 154 expanded)
%              Number of leaves         :   24 ( 300 expanded)
%              Depth                    :   28
%              Number of atoms          : 1177 (9628 expanded)
%              Number of equality atoms :  261 (1431 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(rectify,[],[f3])).

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
    inference(ennf_transformation,[],[f17])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f40,plain,(
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

fof(f41,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f23,f40])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f41])).

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
    inference(flattening,[],[f47])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f38,plain,(
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
    inference(flattening,[],[f38])).

fof(f63,plain,(
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

fof(f62,plain,(
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

fof(f61,plain,(
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

fof(f60,plain,(
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

fof(f59,plain,(
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

fof(f58,plain,(
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

fof(f57,plain,
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

fof(f64,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f39,f63,f62,f61,f60,f59,f58,f57])).

fof(f106,plain,(
    m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f81,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f99,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f65,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f104,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f93,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f110,plain,(
    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
    inference(cnf_transformation,[],[f64])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f82,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f114,plain,(
    r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
    inference(cnf_transformation,[],[f64])).

fof(f113,plain,(
    sK9 = sK10 ),
    inference(cnf_transformation,[],[f64])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f31])).

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
    inference(flattening,[],[f54])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(flattening,[],[f36])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f37])).

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
    inference(cnf_transformation,[],[f56])).

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
    inference(cnf_transformation,[],[f64])).

fof(f107,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f64])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f100,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f101,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f102,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f105,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f64])).

fof(f109,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f64])).

fof(f97,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f98,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f103,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f64])).

fof(f111,plain,(
    m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f64])).

fof(f115,plain,(
    ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
    inference(cnf_transformation,[],[f64])).

fof(f112,plain,(
    m1_subset_1(sK10,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_13,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7125,plain,
    ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_41,negated_conjecture,
    ( m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3094,plain,
    ( m1_pre_topc(sK7,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3109,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4987,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3094,c_3109])).

cnf(c_48,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_53,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_5154,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4987,c_53])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3123,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5394,plain,
    ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = sK7
    | v1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5154,c_3123])).

cnf(c_43,negated_conjecture,
    ( m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3092,plain,
    ( m1_pre_topc(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_4988,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3092,c_3109])).

cnf(c_28,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3101,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_37,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_283,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_16])).

cnf(c_284,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_283])).

cnf(c_3084,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_4152,plain,
    ( m1_pre_topc(X0,sK6) != iProver_top
    | m1_pre_topc(X0,sK7) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_37,c_3084])).

cnf(c_4411,plain,
    ( m1_pre_topc(sK6,sK7) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3101,c_4152])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3103,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5524,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4411,c_3103])).

cnf(c_5528,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v1_pre_topc(sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5524,c_37])).

cnf(c_5836,plain,
    ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5394,c_53,c_4987,c_4988,c_5528])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3106,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5965,plain,
    ( g1_pre_topc(X0,X1) != sK7
    | u1_struct_0(sK6) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_37,c_3106])).

cnf(c_6011,plain,
    ( u1_struct_0(sK7) = u1_struct_0(sK6)
    | m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5836,c_5965])).

cnf(c_17,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3716,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3721,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3716])).

cnf(c_6683,plain,
    ( u1_struct_0(sK7) = u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6011,c_53,c_3721,c_4987])).

cnf(c_33,negated_conjecture,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_3098,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_34,negated_conjecture,
    ( sK9 = sK10 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3161,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3098,c_34])).

cnf(c_14,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_25,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_27,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_274,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_27])).

cnf(c_275,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_274])).

cnf(c_594,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r2_hidden(X2,u1_pre_topc(X3))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | X1 != X3
    | u1_struct_0(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_275])).

cnf(c_595,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_599,plain,
    ( v1_tsep_1(X0,X1)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_595,c_27])).

cnf(c_30,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_729,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_39])).

cnf(c_730,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v1_funct_1(sK8)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_729])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_734,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ v1_tsep_1(X0,X3)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_730,c_40])).

cnf(c_735,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(renaming,[status(thm)],[c_734])).

cnf(c_29,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_778,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_735,c_29])).

cnf(c_801,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X6))
    | ~ m1_pre_topc(X5,X6)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X0 != X5
    | X3 != X6
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(resolution_lifted,[status(thm)],[c_599,c_778])).

cnf(c_802,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X3))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_801])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_846,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X3))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_802,c_16,c_1])).

cnf(c_3083,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK8),X4) != iProver_top
    | r1_tmap_1(X1,X0,sK8,X4) = iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | r2_hidden(u1_struct_0(X2),u1_pre_topc(X1)) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X1,X3) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X3) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_846])).

cnf(c_4050,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK7)
    | r1_tmap_1(X1,sK5,k3_tmap_1(X2,sK5,X0,X1,sK8),X3) != iProver_top
    | r1_tmap_1(X0,sK5,sK8,X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3083])).

cnf(c_47,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_54,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_55,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_56,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_4126,plain,
    ( l1_pre_topc(X2) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | r1_tmap_1(X0,sK5,sK8,X3) = iProver_top
    | r1_tmap_1(X1,sK5,k3_tmap_1(X2,sK5,X0,X1,sK8),X3) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | v2_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4050,c_54,c_55,c_56])).

cnf(c_4127,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK7)
    | r1_tmap_1(X1,sK5,k3_tmap_1(X2,sK5,X0,X1,sK8),X3) != iProver_top
    | r1_tmap_1(X0,sK5,sK8,X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4126])).

cnf(c_4144,plain,
    ( r1_tmap_1(X0,sK5,k3_tmap_1(X1,sK5,sK7,X0,sK8),X2) != iProver_top
    | r1_tmap_1(sK7,sK5,sK8,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_pre_topc(sK7,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4127])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_59,plain,
    ( v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_63,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4531,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_pre_topc(sK7,X1) != iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
    | r1_tmap_1(X0,sK5,k3_tmap_1(X1,sK5,sK7,X0,sK8),X2) != iProver_top
    | r1_tmap_1(sK7,sK5,sK8,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4144,c_59,c_63])).

cnf(c_4532,plain,
    ( r1_tmap_1(X0,sK5,k3_tmap_1(X1,sK5,sK7,X0,sK8),X2) != iProver_top
    | r1_tmap_1(sK7,sK5,sK8,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_pre_topc(sK7,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4531])).

cnf(c_4548,plain,
    ( r1_tmap_1(sK7,sK5,sK8,sK9) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(sK6,sK7) != iProver_top
    | m1_pre_topc(sK7,sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3161,c_4532])).

cnf(c_50,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_51,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_49,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_52,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_44,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_57,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_60,plain,
    ( m1_pre_topc(sK7,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_64,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_32,negated_conjecture,
    ( ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_67,plain,
    ( r1_tmap_1(sK7,sK5,sK8,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_3097,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3148,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3097,c_34])).

cnf(c_4653,plain,
    ( m1_pre_topc(sK6,sK7) != iProver_top
    | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4548,c_51,c_52,c_53,c_57,c_60,c_64,c_67,c_3148])).

cnf(c_4654,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(sK6,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_4653])).

cnf(c_6689,plain,
    ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(sK6,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6683,c_4654])).

cnf(c_6716,plain,
    ( ~ r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
    | ~ m1_pre_topc(sK6,sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6689])).

cnf(c_4159,plain,
    ( ~ m1_pre_topc(sK7,X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK7)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5300,plain,
    ( ~ m1_pre_topc(sK7,sK4)
    | ~ v2_pre_topc(sK4)
    | v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_4159])).

cnf(c_4999,plain,
    ( ~ l1_pre_topc(sK4)
    | l1_pre_topc(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4988])).

cnf(c_4998,plain,
    ( ~ l1_pre_topc(sK4)
    | l1_pre_topc(sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4987])).

cnf(c_4412,plain,
    ( m1_pre_topc(sK6,sK7)
    | ~ l1_pre_topc(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4411])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7125,c_6716,c_5300,c_4999,c_4998,c_4412,c_41,c_48,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:50:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.91/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/0.99  
% 2.91/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.91/0.99  
% 2.91/0.99  ------  iProver source info
% 2.91/0.99  
% 2.91/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.91/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.91/0.99  git: non_committed_changes: false
% 2.91/0.99  git: last_make_outside_of_git: false
% 2.91/0.99  
% 2.91/0.99  ------ 
% 2.91/0.99  
% 2.91/0.99  ------ Input Options
% 2.91/0.99  
% 2.91/0.99  --out_options                           all
% 2.91/0.99  --tptp_safe_out                         true
% 2.91/0.99  --problem_path                          ""
% 2.91/0.99  --include_path                          ""
% 2.91/0.99  --clausifier                            res/vclausify_rel
% 2.91/0.99  --clausifier_options                    --mode clausify
% 2.91/0.99  --stdin                                 false
% 2.91/0.99  --stats_out                             all
% 2.91/0.99  
% 2.91/0.99  ------ General Options
% 2.91/0.99  
% 2.91/0.99  --fof                                   false
% 2.91/0.99  --time_out_real                         305.
% 2.91/0.99  --time_out_virtual                      -1.
% 2.91/0.99  --symbol_type_check                     false
% 2.91/0.99  --clausify_out                          false
% 2.91/0.99  --sig_cnt_out                           false
% 2.91/0.99  --trig_cnt_out                          false
% 2.91/0.99  --trig_cnt_out_tolerance                1.
% 2.91/0.99  --trig_cnt_out_sk_spl                   false
% 2.91/0.99  --abstr_cl_out                          false
% 2.91/0.99  
% 2.91/0.99  ------ Global Options
% 2.91/0.99  
% 2.91/0.99  --schedule                              default
% 2.91/0.99  --add_important_lit                     false
% 2.91/0.99  --prop_solver_per_cl                    1000
% 2.91/0.99  --min_unsat_core                        false
% 2.91/0.99  --soft_assumptions                      false
% 2.91/0.99  --soft_lemma_size                       3
% 2.91/0.99  --prop_impl_unit_size                   0
% 2.91/0.99  --prop_impl_unit                        []
% 2.91/0.99  --share_sel_clauses                     true
% 2.91/0.99  --reset_solvers                         false
% 2.91/0.99  --bc_imp_inh                            [conj_cone]
% 2.91/0.99  --conj_cone_tolerance                   3.
% 2.91/0.99  --extra_neg_conj                        none
% 2.91/0.99  --large_theory_mode                     true
% 2.91/0.99  --prolific_symb_bound                   200
% 2.91/0.99  --lt_threshold                          2000
% 2.91/0.99  --clause_weak_htbl                      true
% 2.91/0.99  --gc_record_bc_elim                     false
% 2.91/0.99  
% 2.91/0.99  ------ Preprocessing Options
% 2.91/0.99  
% 2.91/0.99  --preprocessing_flag                    true
% 2.91/0.99  --time_out_prep_mult                    0.1
% 2.91/0.99  --splitting_mode                        input
% 2.91/0.99  --splitting_grd                         true
% 2.91/0.99  --splitting_cvd                         false
% 2.91/0.99  --splitting_cvd_svl                     false
% 2.91/0.99  --splitting_nvd                         32
% 2.91/0.99  --sub_typing                            true
% 2.91/0.99  --prep_gs_sim                           true
% 2.91/0.99  --prep_unflatten                        true
% 2.91/0.99  --prep_res_sim                          true
% 2.91/0.99  --prep_upred                            true
% 2.91/0.99  --prep_sem_filter                       exhaustive
% 2.91/0.99  --prep_sem_filter_out                   false
% 2.91/0.99  --pred_elim                             true
% 2.91/0.99  --res_sim_input                         true
% 2.91/0.99  --eq_ax_congr_red                       true
% 2.91/0.99  --pure_diseq_elim                       true
% 2.91/0.99  --brand_transform                       false
% 2.91/0.99  --non_eq_to_eq                          false
% 2.91/0.99  --prep_def_merge                        true
% 2.91/0.99  --prep_def_merge_prop_impl              false
% 2.91/1.00  --prep_def_merge_mbd                    true
% 2.91/1.00  --prep_def_merge_tr_red                 false
% 2.91/1.00  --prep_def_merge_tr_cl                  false
% 2.91/1.00  --smt_preprocessing                     true
% 2.91/1.00  --smt_ac_axioms                         fast
% 2.91/1.00  --preprocessed_out                      false
% 2.91/1.00  --preprocessed_stats                    false
% 2.91/1.00  
% 2.91/1.00  ------ Abstraction refinement Options
% 2.91/1.00  
% 2.91/1.00  --abstr_ref                             []
% 2.91/1.00  --abstr_ref_prep                        false
% 2.91/1.00  --abstr_ref_until_sat                   false
% 2.91/1.00  --abstr_ref_sig_restrict                funpre
% 2.91/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.91/1.00  --abstr_ref_under                       []
% 2.91/1.00  
% 2.91/1.00  ------ SAT Options
% 2.91/1.00  
% 2.91/1.00  --sat_mode                              false
% 2.91/1.00  --sat_fm_restart_options                ""
% 2.91/1.00  --sat_gr_def                            false
% 2.91/1.00  --sat_epr_types                         true
% 2.91/1.00  --sat_non_cyclic_types                  false
% 2.91/1.00  --sat_finite_models                     false
% 2.91/1.00  --sat_fm_lemmas                         false
% 2.91/1.00  --sat_fm_prep                           false
% 2.91/1.00  --sat_fm_uc_incr                        true
% 2.91/1.00  --sat_out_model                         small
% 2.91/1.00  --sat_out_clauses                       false
% 2.91/1.00  
% 2.91/1.00  ------ QBF Options
% 2.91/1.00  
% 2.91/1.00  --qbf_mode                              false
% 2.91/1.00  --qbf_elim_univ                         false
% 2.91/1.00  --qbf_dom_inst                          none
% 2.91/1.00  --qbf_dom_pre_inst                      false
% 2.91/1.00  --qbf_sk_in                             false
% 2.91/1.00  --qbf_pred_elim                         true
% 2.91/1.00  --qbf_split                             512
% 2.91/1.00  
% 2.91/1.00  ------ BMC1 Options
% 2.91/1.00  
% 2.91/1.00  --bmc1_incremental                      false
% 2.91/1.00  --bmc1_axioms                           reachable_all
% 2.91/1.00  --bmc1_min_bound                        0
% 2.91/1.00  --bmc1_max_bound                        -1
% 2.91/1.00  --bmc1_max_bound_default                -1
% 2.91/1.00  --bmc1_symbol_reachability              true
% 2.91/1.00  --bmc1_property_lemmas                  false
% 2.91/1.00  --bmc1_k_induction                      false
% 2.91/1.00  --bmc1_non_equiv_states                 false
% 2.91/1.00  --bmc1_deadlock                         false
% 2.91/1.00  --bmc1_ucm                              false
% 2.91/1.00  --bmc1_add_unsat_core                   none
% 2.91/1.00  --bmc1_unsat_core_children              false
% 2.91/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.91/1.00  --bmc1_out_stat                         full
% 2.91/1.00  --bmc1_ground_init                      false
% 2.91/1.00  --bmc1_pre_inst_next_state              false
% 2.91/1.00  --bmc1_pre_inst_state                   false
% 2.91/1.00  --bmc1_pre_inst_reach_state             false
% 2.91/1.00  --bmc1_out_unsat_core                   false
% 2.91/1.00  --bmc1_aig_witness_out                  false
% 2.91/1.00  --bmc1_verbose                          false
% 2.91/1.00  --bmc1_dump_clauses_tptp                false
% 2.91/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.91/1.00  --bmc1_dump_file                        -
% 2.91/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.91/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.91/1.00  --bmc1_ucm_extend_mode                  1
% 2.91/1.00  --bmc1_ucm_init_mode                    2
% 2.91/1.00  --bmc1_ucm_cone_mode                    none
% 2.91/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.91/1.00  --bmc1_ucm_relax_model                  4
% 2.91/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.91/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.91/1.00  --bmc1_ucm_layered_model                none
% 2.91/1.00  --bmc1_ucm_max_lemma_size               10
% 2.91/1.00  
% 2.91/1.00  ------ AIG Options
% 2.91/1.00  
% 2.91/1.00  --aig_mode                              false
% 2.91/1.00  
% 2.91/1.00  ------ Instantiation Options
% 2.91/1.00  
% 2.91/1.00  --instantiation_flag                    true
% 2.91/1.00  --inst_sos_flag                         false
% 2.91/1.00  --inst_sos_phase                        true
% 2.91/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.91/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.91/1.00  --inst_lit_sel_side                     num_symb
% 2.91/1.00  --inst_solver_per_active                1400
% 2.91/1.00  --inst_solver_calls_frac                1.
% 2.91/1.00  --inst_passive_queue_type               priority_queues
% 2.91/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.91/1.00  --inst_passive_queues_freq              [25;2]
% 2.91/1.00  --inst_dismatching                      true
% 2.91/1.00  --inst_eager_unprocessed_to_passive     true
% 2.91/1.00  --inst_prop_sim_given                   true
% 2.91/1.00  --inst_prop_sim_new                     false
% 2.91/1.00  --inst_subs_new                         false
% 2.91/1.00  --inst_eq_res_simp                      false
% 2.91/1.00  --inst_subs_given                       false
% 2.91/1.00  --inst_orphan_elimination               true
% 2.91/1.00  --inst_learning_loop_flag               true
% 2.91/1.00  --inst_learning_start                   3000
% 2.91/1.00  --inst_learning_factor                  2
% 2.91/1.00  --inst_start_prop_sim_after_learn       3
% 2.91/1.00  --inst_sel_renew                        solver
% 2.91/1.00  --inst_lit_activity_flag                true
% 2.91/1.00  --inst_restr_to_given                   false
% 2.91/1.00  --inst_activity_threshold               500
% 2.91/1.00  --inst_out_proof                        true
% 2.91/1.00  
% 2.91/1.00  ------ Resolution Options
% 2.91/1.00  
% 2.91/1.00  --resolution_flag                       true
% 2.91/1.00  --res_lit_sel                           adaptive
% 2.91/1.00  --res_lit_sel_side                      none
% 2.91/1.00  --res_ordering                          kbo
% 2.91/1.00  --res_to_prop_solver                    active
% 2.91/1.00  --res_prop_simpl_new                    false
% 2.91/1.00  --res_prop_simpl_given                  true
% 2.91/1.00  --res_passive_queue_type                priority_queues
% 2.91/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.91/1.00  --res_passive_queues_freq               [15;5]
% 2.91/1.00  --res_forward_subs                      full
% 2.91/1.00  --res_backward_subs                     full
% 2.91/1.00  --res_forward_subs_resolution           true
% 2.91/1.00  --res_backward_subs_resolution          true
% 2.91/1.00  --res_orphan_elimination                true
% 2.91/1.00  --res_time_limit                        2.
% 2.91/1.00  --res_out_proof                         true
% 2.91/1.00  
% 2.91/1.00  ------ Superposition Options
% 2.91/1.00  
% 2.91/1.00  --superposition_flag                    true
% 2.91/1.00  --sup_passive_queue_type                priority_queues
% 2.91/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.91/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.91/1.00  --demod_completeness_check              fast
% 2.91/1.00  --demod_use_ground                      true
% 2.91/1.00  --sup_to_prop_solver                    passive
% 2.91/1.00  --sup_prop_simpl_new                    true
% 2.91/1.00  --sup_prop_simpl_given                  true
% 2.91/1.00  --sup_fun_splitting                     false
% 2.91/1.00  --sup_smt_interval                      50000
% 2.91/1.00  
% 2.91/1.00  ------ Superposition Simplification Setup
% 2.91/1.00  
% 2.91/1.00  --sup_indices_passive                   []
% 2.91/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.91/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.00  --sup_full_bw                           [BwDemod]
% 2.91/1.00  --sup_immed_triv                        [TrivRules]
% 2.91/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.91/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.00  --sup_immed_bw_main                     []
% 2.91/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.91/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/1.00  
% 2.91/1.00  ------ Combination Options
% 2.91/1.00  
% 2.91/1.00  --comb_res_mult                         3
% 2.91/1.00  --comb_sup_mult                         2
% 2.91/1.00  --comb_inst_mult                        10
% 2.91/1.00  
% 2.91/1.00  ------ Debug Options
% 2.91/1.00  
% 2.91/1.00  --dbg_backtrace                         false
% 2.91/1.00  --dbg_dump_prop_clauses                 false
% 2.91/1.00  --dbg_dump_prop_clauses_file            -
% 2.91/1.00  --dbg_out_stat                          false
% 2.91/1.00  ------ Parsing...
% 2.91/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.91/1.00  
% 2.91/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.91/1.00  
% 2.91/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.91/1.00  
% 2.91/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.91/1.00  ------ Proving...
% 2.91/1.00  ------ Problem Properties 
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  clauses                                 44
% 2.91/1.00  conjectures                             17
% 2.91/1.00  EPR                                     17
% 2.91/1.00  Horn                                    36
% 2.91/1.00  unary                                   17
% 2.91/1.00  binary                                  7
% 2.91/1.00  lits                                    136
% 2.91/1.00  lits eq                                 11
% 2.91/1.00  fd_pure                                 0
% 2.91/1.00  fd_pseudo                               0
% 2.91/1.00  fd_cond                                 0
% 2.91/1.00  fd_pseudo_cond                          2
% 2.91/1.00  AC symbols                              0
% 2.91/1.00  
% 2.91/1.00  ------ Schedule dynamic 5 is on 
% 2.91/1.00  
% 2.91/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  ------ 
% 2.91/1.00  Current options:
% 2.91/1.00  ------ 
% 2.91/1.00  
% 2.91/1.00  ------ Input Options
% 2.91/1.00  
% 2.91/1.00  --out_options                           all
% 2.91/1.00  --tptp_safe_out                         true
% 2.91/1.00  --problem_path                          ""
% 2.91/1.00  --include_path                          ""
% 2.91/1.00  --clausifier                            res/vclausify_rel
% 2.91/1.00  --clausifier_options                    --mode clausify
% 2.91/1.00  --stdin                                 false
% 2.91/1.00  --stats_out                             all
% 2.91/1.00  
% 2.91/1.00  ------ General Options
% 2.91/1.00  
% 2.91/1.00  --fof                                   false
% 2.91/1.00  --time_out_real                         305.
% 2.91/1.00  --time_out_virtual                      -1.
% 2.91/1.00  --symbol_type_check                     false
% 2.91/1.00  --clausify_out                          false
% 2.91/1.00  --sig_cnt_out                           false
% 2.91/1.00  --trig_cnt_out                          false
% 2.91/1.00  --trig_cnt_out_tolerance                1.
% 2.91/1.00  --trig_cnt_out_sk_spl                   false
% 2.91/1.00  --abstr_cl_out                          false
% 2.91/1.00  
% 2.91/1.00  ------ Global Options
% 2.91/1.00  
% 2.91/1.00  --schedule                              default
% 2.91/1.00  --add_important_lit                     false
% 2.91/1.00  --prop_solver_per_cl                    1000
% 2.91/1.00  --min_unsat_core                        false
% 2.91/1.00  --soft_assumptions                      false
% 2.91/1.00  --soft_lemma_size                       3
% 2.91/1.00  --prop_impl_unit_size                   0
% 2.91/1.00  --prop_impl_unit                        []
% 2.91/1.00  --share_sel_clauses                     true
% 2.91/1.00  --reset_solvers                         false
% 2.91/1.00  --bc_imp_inh                            [conj_cone]
% 2.91/1.00  --conj_cone_tolerance                   3.
% 2.91/1.00  --extra_neg_conj                        none
% 2.91/1.00  --large_theory_mode                     true
% 2.91/1.00  --prolific_symb_bound                   200
% 2.91/1.00  --lt_threshold                          2000
% 2.91/1.00  --clause_weak_htbl                      true
% 2.91/1.00  --gc_record_bc_elim                     false
% 2.91/1.00  
% 2.91/1.00  ------ Preprocessing Options
% 2.91/1.00  
% 2.91/1.00  --preprocessing_flag                    true
% 2.91/1.00  --time_out_prep_mult                    0.1
% 2.91/1.00  --splitting_mode                        input
% 2.91/1.00  --splitting_grd                         true
% 2.91/1.00  --splitting_cvd                         false
% 2.91/1.00  --splitting_cvd_svl                     false
% 2.91/1.00  --splitting_nvd                         32
% 2.91/1.00  --sub_typing                            true
% 2.91/1.00  --prep_gs_sim                           true
% 2.91/1.00  --prep_unflatten                        true
% 2.91/1.00  --prep_res_sim                          true
% 2.91/1.00  --prep_upred                            true
% 2.91/1.00  --prep_sem_filter                       exhaustive
% 2.91/1.00  --prep_sem_filter_out                   false
% 2.91/1.00  --pred_elim                             true
% 2.91/1.00  --res_sim_input                         true
% 2.91/1.00  --eq_ax_congr_red                       true
% 2.91/1.00  --pure_diseq_elim                       true
% 2.91/1.00  --brand_transform                       false
% 2.91/1.00  --non_eq_to_eq                          false
% 2.91/1.00  --prep_def_merge                        true
% 2.91/1.00  --prep_def_merge_prop_impl              false
% 2.91/1.00  --prep_def_merge_mbd                    true
% 2.91/1.00  --prep_def_merge_tr_red                 false
% 2.91/1.00  --prep_def_merge_tr_cl                  false
% 2.91/1.00  --smt_preprocessing                     true
% 2.91/1.00  --smt_ac_axioms                         fast
% 2.91/1.00  --preprocessed_out                      false
% 2.91/1.00  --preprocessed_stats                    false
% 2.91/1.00  
% 2.91/1.00  ------ Abstraction refinement Options
% 2.91/1.00  
% 2.91/1.00  --abstr_ref                             []
% 2.91/1.00  --abstr_ref_prep                        false
% 2.91/1.00  --abstr_ref_until_sat                   false
% 2.91/1.00  --abstr_ref_sig_restrict                funpre
% 2.91/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.91/1.00  --abstr_ref_under                       []
% 2.91/1.00  
% 2.91/1.00  ------ SAT Options
% 2.91/1.00  
% 2.91/1.00  --sat_mode                              false
% 2.91/1.00  --sat_fm_restart_options                ""
% 2.91/1.00  --sat_gr_def                            false
% 2.91/1.00  --sat_epr_types                         true
% 2.91/1.00  --sat_non_cyclic_types                  false
% 2.91/1.00  --sat_finite_models                     false
% 2.91/1.00  --sat_fm_lemmas                         false
% 2.91/1.00  --sat_fm_prep                           false
% 2.91/1.00  --sat_fm_uc_incr                        true
% 2.91/1.00  --sat_out_model                         small
% 2.91/1.00  --sat_out_clauses                       false
% 2.91/1.00  
% 2.91/1.00  ------ QBF Options
% 2.91/1.00  
% 2.91/1.00  --qbf_mode                              false
% 2.91/1.00  --qbf_elim_univ                         false
% 2.91/1.00  --qbf_dom_inst                          none
% 2.91/1.00  --qbf_dom_pre_inst                      false
% 2.91/1.00  --qbf_sk_in                             false
% 2.91/1.00  --qbf_pred_elim                         true
% 2.91/1.00  --qbf_split                             512
% 2.91/1.00  
% 2.91/1.00  ------ BMC1 Options
% 2.91/1.00  
% 2.91/1.00  --bmc1_incremental                      false
% 2.91/1.00  --bmc1_axioms                           reachable_all
% 2.91/1.00  --bmc1_min_bound                        0
% 2.91/1.00  --bmc1_max_bound                        -1
% 2.91/1.00  --bmc1_max_bound_default                -1
% 2.91/1.00  --bmc1_symbol_reachability              true
% 2.91/1.00  --bmc1_property_lemmas                  false
% 2.91/1.00  --bmc1_k_induction                      false
% 2.91/1.00  --bmc1_non_equiv_states                 false
% 2.91/1.00  --bmc1_deadlock                         false
% 2.91/1.00  --bmc1_ucm                              false
% 2.91/1.00  --bmc1_add_unsat_core                   none
% 2.91/1.00  --bmc1_unsat_core_children              false
% 2.91/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.91/1.00  --bmc1_out_stat                         full
% 2.91/1.00  --bmc1_ground_init                      false
% 2.91/1.00  --bmc1_pre_inst_next_state              false
% 2.91/1.00  --bmc1_pre_inst_state                   false
% 2.91/1.00  --bmc1_pre_inst_reach_state             false
% 2.91/1.00  --bmc1_out_unsat_core                   false
% 2.91/1.00  --bmc1_aig_witness_out                  false
% 2.91/1.00  --bmc1_verbose                          false
% 2.91/1.00  --bmc1_dump_clauses_tptp                false
% 2.91/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.91/1.00  --bmc1_dump_file                        -
% 2.91/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.91/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.91/1.00  --bmc1_ucm_extend_mode                  1
% 2.91/1.00  --bmc1_ucm_init_mode                    2
% 2.91/1.00  --bmc1_ucm_cone_mode                    none
% 2.91/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.91/1.00  --bmc1_ucm_relax_model                  4
% 2.91/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.91/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.91/1.00  --bmc1_ucm_layered_model                none
% 2.91/1.00  --bmc1_ucm_max_lemma_size               10
% 2.91/1.00  
% 2.91/1.00  ------ AIG Options
% 2.91/1.00  
% 2.91/1.00  --aig_mode                              false
% 2.91/1.00  
% 2.91/1.00  ------ Instantiation Options
% 2.91/1.00  
% 2.91/1.00  --instantiation_flag                    true
% 2.91/1.00  --inst_sos_flag                         false
% 2.91/1.00  --inst_sos_phase                        true
% 2.91/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.91/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.91/1.00  --inst_lit_sel_side                     none
% 2.91/1.00  --inst_solver_per_active                1400
% 2.91/1.00  --inst_solver_calls_frac                1.
% 2.91/1.00  --inst_passive_queue_type               priority_queues
% 2.91/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.91/1.00  --inst_passive_queues_freq              [25;2]
% 2.91/1.00  --inst_dismatching                      true
% 2.91/1.00  --inst_eager_unprocessed_to_passive     true
% 2.91/1.00  --inst_prop_sim_given                   true
% 2.91/1.00  --inst_prop_sim_new                     false
% 2.91/1.00  --inst_subs_new                         false
% 2.91/1.00  --inst_eq_res_simp                      false
% 2.91/1.00  --inst_subs_given                       false
% 2.91/1.00  --inst_orphan_elimination               true
% 2.91/1.00  --inst_learning_loop_flag               true
% 2.91/1.00  --inst_learning_start                   3000
% 2.91/1.00  --inst_learning_factor                  2
% 2.91/1.00  --inst_start_prop_sim_after_learn       3
% 2.91/1.00  --inst_sel_renew                        solver
% 2.91/1.00  --inst_lit_activity_flag                true
% 2.91/1.00  --inst_restr_to_given                   false
% 2.91/1.00  --inst_activity_threshold               500
% 2.91/1.00  --inst_out_proof                        true
% 2.91/1.00  
% 2.91/1.00  ------ Resolution Options
% 2.91/1.00  
% 2.91/1.00  --resolution_flag                       false
% 2.91/1.00  --res_lit_sel                           adaptive
% 2.91/1.00  --res_lit_sel_side                      none
% 2.91/1.00  --res_ordering                          kbo
% 2.91/1.00  --res_to_prop_solver                    active
% 2.91/1.00  --res_prop_simpl_new                    false
% 2.91/1.00  --res_prop_simpl_given                  true
% 2.91/1.00  --res_passive_queue_type                priority_queues
% 2.91/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.91/1.00  --res_passive_queues_freq               [15;5]
% 2.91/1.00  --res_forward_subs                      full
% 2.91/1.00  --res_backward_subs                     full
% 2.91/1.00  --res_forward_subs_resolution           true
% 2.91/1.00  --res_backward_subs_resolution          true
% 2.91/1.00  --res_orphan_elimination                true
% 2.91/1.00  --res_time_limit                        2.
% 2.91/1.00  --res_out_proof                         true
% 2.91/1.00  
% 2.91/1.00  ------ Superposition Options
% 2.91/1.00  
% 2.91/1.00  --superposition_flag                    true
% 2.91/1.00  --sup_passive_queue_type                priority_queues
% 2.91/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.91/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.91/1.00  --demod_completeness_check              fast
% 2.91/1.00  --demod_use_ground                      true
% 2.91/1.00  --sup_to_prop_solver                    passive
% 2.91/1.00  --sup_prop_simpl_new                    true
% 2.91/1.00  --sup_prop_simpl_given                  true
% 2.91/1.00  --sup_fun_splitting                     false
% 2.91/1.00  --sup_smt_interval                      50000
% 2.91/1.00  
% 2.91/1.00  ------ Superposition Simplification Setup
% 2.91/1.00  
% 2.91/1.00  --sup_indices_passive                   []
% 2.91/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.91/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.00  --sup_full_bw                           [BwDemod]
% 2.91/1.00  --sup_immed_triv                        [TrivRules]
% 2.91/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.91/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.00  --sup_immed_bw_main                     []
% 2.91/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.91/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/1.00  
% 2.91/1.00  ------ Combination Options
% 2.91/1.00  
% 2.91/1.00  --comb_res_mult                         3
% 2.91/1.00  --comb_sup_mult                         2
% 2.91/1.00  --comb_inst_mult                        10
% 2.91/1.00  
% 2.91/1.00  ------ Debug Options
% 2.91/1.00  
% 2.91/1.00  --dbg_backtrace                         false
% 2.91/1.00  --dbg_dump_prop_clauses                 false
% 2.91/1.00  --dbg_dump_prop_clauses_file            -
% 2.91/1.00  --dbg_out_stat                          false
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  ------ Proving...
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  % SZS status Theorem for theBenchmark.p
% 2.91/1.00  
% 2.91/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.91/1.00  
% 2.91/1.00  fof(f3,axiom,(
% 2.91/1.00    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f17,plain,(
% 2.91/1.00    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.91/1.00    inference(rectify,[],[f3])).
% 2.91/1.00  
% 2.91/1.00  fof(f22,plain,(
% 2.91/1.00    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.91/1.00    inference(ennf_transformation,[],[f17])).
% 2.91/1.00  
% 2.91/1.00  fof(f23,plain,(
% 2.91/1.00    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.91/1.00    inference(flattening,[],[f22])).
% 2.91/1.00  
% 2.91/1.00  fof(f40,plain,(
% 2.91/1.00    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.91/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.91/1.00  
% 2.91/1.00  fof(f41,plain,(
% 2.91/1.00    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.91/1.00    inference(definition_folding,[],[f23,f40])).
% 2.91/1.00  
% 2.91/1.00  fof(f47,plain,(
% 2.91/1.00    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.91/1.00    inference(nnf_transformation,[],[f41])).
% 2.91/1.00  
% 2.91/1.00  fof(f48,plain,(
% 2.91/1.00    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.91/1.00    inference(flattening,[],[f47])).
% 2.91/1.00  
% 2.91/1.00  fof(f49,plain,(
% 2.91/1.00    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.91/1.00    inference(rectify,[],[f48])).
% 2.91/1.00  
% 2.91/1.00  fof(f50,plain,(
% 2.91/1.00    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.91/1.00    introduced(choice_axiom,[])).
% 2.91/1.00  
% 2.91/1.00  fof(f51,plain,(
% 2.91/1.00    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.91/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).
% 2.91/1.00  
% 2.91/1.00  fof(f73,plain,(
% 2.91/1.00    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f51])).
% 2.91/1.00  
% 2.91/1.00  fof(f15,conjecture,(
% 2.91/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f16,negated_conjecture,(
% 2.91/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 2.91/1.00    inference(negated_conjecture,[],[f15])).
% 2.91/1.00  
% 2.91/1.00  fof(f38,plain,(
% 2.91/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.91/1.00    inference(ennf_transformation,[],[f16])).
% 2.91/1.00  
% 2.91/1.00  fof(f39,plain,(
% 2.91/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.91/1.00    inference(flattening,[],[f38])).
% 2.91/1.00  
% 2.91/1.00  fof(f63,plain,(
% 2.91/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK10) & sK10 = X5 & m1_subset_1(sK10,u1_struct_0(X2)))) )),
% 2.91/1.00    introduced(choice_axiom,[])).
% 2.91/1.00  
% 2.91/1.00  fof(f62,plain,(
% 2.91/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK9) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK9 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK9,u1_struct_0(X3)))) )),
% 2.91/1.00    introduced(choice_axiom,[])).
% 2.91/1.00  
% 2.91/1.00  fof(f61,plain,(
% 2.91/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK8,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK8),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK8,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK8))) )),
% 2.91/1.00    introduced(choice_axiom,[])).
% 2.91/1.00  
% 2.91/1.00  fof(f60,plain,(
% 2.91/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK7,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK7,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK7))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK7 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK7,X0) & ~v2_struct_0(sK7))) )),
% 2.91/1.00    introduced(choice_axiom,[])).
% 2.91/1.00  
% 2.91/1.00  fof(f59,plain,(
% 2.91/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK6,X1,k3_tmap_1(X0,X1,X3,sK6,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK6))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 2.91/1.00    introduced(choice_axiom,[])).
% 2.91/1.00  
% 2.91/1.00  fof(f58,plain,(
% 2.91/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK5,X4,X5) & r1_tmap_1(X2,sK5,k3_tmap_1(X0,sK5,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))) )),
% 2.91/1.00    introduced(choice_axiom,[])).
% 2.91/1.00  
% 2.91/1.00  fof(f57,plain,(
% 2.91/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK4,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 2.91/1.00    introduced(choice_axiom,[])).
% 2.91/1.00  
% 2.91/1.00  fof(f64,plain,(
% 2.91/1.00    ((((((~r1_tmap_1(sK7,sK5,sK8,sK9) & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) & sK9 = sK10 & m1_subset_1(sK10,u1_struct_0(sK6))) & m1_subset_1(sK9,u1_struct_0(sK7))) & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(sK8)) & m1_pre_topc(sK7,sK4) & ~v2_struct_0(sK7)) & m1_pre_topc(sK6,sK4) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 2.91/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f39,f63,f62,f61,f60,f59,f58,f57])).
% 2.91/1.00  
% 2.91/1.00  fof(f106,plain,(
% 2.91/1.00    m1_pre_topc(sK7,sK4)),
% 2.91/1.00    inference(cnf_transformation,[],[f64])).
% 2.91/1.00  
% 2.91/1.00  fof(f5,axiom,(
% 2.91/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f25,plain,(
% 2.91/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.91/1.00    inference(ennf_transformation,[],[f5])).
% 2.91/1.00  
% 2.91/1.00  fof(f81,plain,(
% 2.91/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f25])).
% 2.91/1.00  
% 2.91/1.00  fof(f99,plain,(
% 2.91/1.00    l1_pre_topc(sK4)),
% 2.91/1.00    inference(cnf_transformation,[],[f64])).
% 2.91/1.00  
% 2.91/1.00  fof(f1,axiom,(
% 2.91/1.00    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f18,plain,(
% 2.91/1.00    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 2.91/1.00    inference(ennf_transformation,[],[f1])).
% 2.91/1.00  
% 2.91/1.00  fof(f19,plain,(
% 2.91/1.00    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.91/1.00    inference(flattening,[],[f18])).
% 2.91/1.00  
% 2.91/1.00  fof(f65,plain,(
% 2.91/1.00    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f19])).
% 2.91/1.00  
% 2.91/1.00  fof(f104,plain,(
% 2.91/1.00    m1_pre_topc(sK6,sK4)),
% 2.91/1.00    inference(cnf_transformation,[],[f64])).
% 2.91/1.00  
% 2.91/1.00  fof(f12,axiom,(
% 2.91/1.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f33,plain,(
% 2.91/1.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.91/1.00    inference(ennf_transformation,[],[f12])).
% 2.91/1.00  
% 2.91/1.00  fof(f93,plain,(
% 2.91/1.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f33])).
% 2.91/1.00  
% 2.91/1.00  fof(f110,plain,(
% 2.91/1.00    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7),
% 2.91/1.00    inference(cnf_transformation,[],[f64])).
% 2.91/1.00  
% 2.91/1.00  fof(f8,axiom,(
% 2.91/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f28,plain,(
% 2.91/1.00    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.91/1.00    inference(ennf_transformation,[],[f8])).
% 2.91/1.00  
% 2.91/1.00  fof(f53,plain,(
% 2.91/1.00    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.91/1.00    inference(nnf_transformation,[],[f28])).
% 2.91/1.00  
% 2.91/1.00  fof(f85,plain,(
% 2.91/1.00    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f53])).
% 2.91/1.00  
% 2.91/1.00  fof(f9,axiom,(
% 2.91/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f29,plain,(
% 2.91/1.00    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.91/1.00    inference(ennf_transformation,[],[f9])).
% 2.91/1.00  
% 2.91/1.00  fof(f87,plain,(
% 2.91/1.00    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f29])).
% 2.91/1.00  
% 2.91/1.00  fof(f7,axiom,(
% 2.91/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f27,plain,(
% 2.91/1.00    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.91/1.00    inference(ennf_transformation,[],[f7])).
% 2.91/1.00  
% 2.91/1.00  fof(f83,plain,(
% 2.91/1.00    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.91/1.00    inference(cnf_transformation,[],[f27])).
% 2.91/1.00  
% 2.91/1.00  fof(f6,axiom,(
% 2.91/1.00    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f26,plain,(
% 2.91/1.00    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.91/1.00    inference(ennf_transformation,[],[f6])).
% 2.91/1.00  
% 2.91/1.00  fof(f82,plain,(
% 2.91/1.00    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f26])).
% 2.91/1.00  
% 2.91/1.00  fof(f114,plain,(
% 2.91/1.00    r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)),
% 2.91/1.00    inference(cnf_transformation,[],[f64])).
% 2.91/1.00  
% 2.91/1.00  fof(f113,plain,(
% 2.91/1.00    sK9 = sK10),
% 2.91/1.00    inference(cnf_transformation,[],[f64])).
% 2.91/1.00  
% 2.91/1.00  fof(f4,axiom,(
% 2.91/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f24,plain,(
% 2.91/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.91/1.00    inference(ennf_transformation,[],[f4])).
% 2.91/1.00  
% 2.91/1.00  fof(f52,plain,(
% 2.91/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.91/1.00    inference(nnf_transformation,[],[f24])).
% 2.91/1.00  
% 2.91/1.00  fof(f80,plain,(
% 2.91/1.00    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f52])).
% 2.91/1.00  
% 2.91/1.00  fof(f10,axiom,(
% 2.91/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f30,plain,(
% 2.91/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.91/1.00    inference(ennf_transformation,[],[f10])).
% 2.91/1.00  
% 2.91/1.00  fof(f31,plain,(
% 2.91/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.91/1.00    inference(flattening,[],[f30])).
% 2.91/1.00  
% 2.91/1.00  fof(f54,plain,(
% 2.91/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.91/1.00    inference(nnf_transformation,[],[f31])).
% 2.91/1.00  
% 2.91/1.00  fof(f55,plain,(
% 2.91/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.91/1.00    inference(flattening,[],[f54])).
% 2.91/1.00  
% 2.91/1.00  fof(f90,plain,(
% 2.91/1.00    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f55])).
% 2.91/1.00  
% 2.91/1.00  fof(f117,plain,(
% 2.91/1.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.91/1.00    inference(equality_resolution,[],[f90])).
% 2.91/1.00  
% 2.91/1.00  fof(f11,axiom,(
% 2.91/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f32,plain,(
% 2.91/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.91/1.00    inference(ennf_transformation,[],[f11])).
% 2.91/1.00  
% 2.91/1.00  fof(f92,plain,(
% 2.91/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f32])).
% 2.91/1.00  
% 2.91/1.00  fof(f14,axiom,(
% 2.91/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f36,plain,(
% 2.91/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.91/1.00    inference(ennf_transformation,[],[f14])).
% 2.91/1.00  
% 2.91/1.00  fof(f37,plain,(
% 2.91/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.91/1.00    inference(flattening,[],[f36])).
% 2.91/1.00  
% 2.91/1.00  fof(f56,plain,(
% 2.91/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.91/1.00    inference(nnf_transformation,[],[f37])).
% 2.91/1.00  
% 2.91/1.00  fof(f96,plain,(
% 2.91/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f56])).
% 2.91/1.00  
% 2.91/1.00  fof(f119,plain,(
% 2.91/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.91/1.00    inference(equality_resolution,[],[f96])).
% 2.91/1.00  
% 2.91/1.00  fof(f108,plain,(
% 2.91/1.00    v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))),
% 2.91/1.00    inference(cnf_transformation,[],[f64])).
% 2.91/1.00  
% 2.91/1.00  fof(f107,plain,(
% 2.91/1.00    v1_funct_1(sK8)),
% 2.91/1.00    inference(cnf_transformation,[],[f64])).
% 2.91/1.00  
% 2.91/1.00  fof(f13,axiom,(
% 2.91/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f34,plain,(
% 2.91/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.91/1.00    inference(ennf_transformation,[],[f13])).
% 2.91/1.00  
% 2.91/1.00  fof(f35,plain,(
% 2.91/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.91/1.00    inference(flattening,[],[f34])).
% 2.91/1.00  
% 2.91/1.00  fof(f94,plain,(
% 2.91/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f35])).
% 2.91/1.00  
% 2.91/1.00  fof(f2,axiom,(
% 2.91/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/1.00  
% 2.91/1.00  fof(f20,plain,(
% 2.91/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.91/1.00    inference(ennf_transformation,[],[f2])).
% 2.91/1.00  
% 2.91/1.00  fof(f21,plain,(
% 2.91/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.91/1.00    inference(flattening,[],[f20])).
% 2.91/1.00  
% 2.91/1.00  fof(f66,plain,(
% 2.91/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.91/1.00    inference(cnf_transformation,[],[f21])).
% 2.91/1.00  
% 2.91/1.00  fof(f100,plain,(
% 2.91/1.00    ~v2_struct_0(sK5)),
% 2.91/1.00    inference(cnf_transformation,[],[f64])).
% 2.91/1.00  
% 2.91/1.00  fof(f101,plain,(
% 2.91/1.00    v2_pre_topc(sK5)),
% 2.91/1.00    inference(cnf_transformation,[],[f64])).
% 2.91/1.00  
% 2.91/1.00  fof(f102,plain,(
% 2.91/1.00    l1_pre_topc(sK5)),
% 2.91/1.00    inference(cnf_transformation,[],[f64])).
% 2.91/1.00  
% 2.91/1.00  fof(f105,plain,(
% 2.91/1.00    ~v2_struct_0(sK7)),
% 2.91/1.00    inference(cnf_transformation,[],[f64])).
% 2.91/1.00  
% 2.91/1.00  fof(f109,plain,(
% 2.91/1.00    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))),
% 2.91/1.00    inference(cnf_transformation,[],[f64])).
% 2.91/1.00  
% 2.91/1.00  fof(f97,plain,(
% 2.91/1.00    ~v2_struct_0(sK4)),
% 2.91/1.00    inference(cnf_transformation,[],[f64])).
% 2.91/1.00  
% 2.91/1.00  fof(f98,plain,(
% 2.91/1.00    v2_pre_topc(sK4)),
% 2.91/1.00    inference(cnf_transformation,[],[f64])).
% 2.91/1.00  
% 2.91/1.00  fof(f103,plain,(
% 2.91/1.00    ~v2_struct_0(sK6)),
% 2.91/1.00    inference(cnf_transformation,[],[f64])).
% 2.91/1.00  
% 2.91/1.00  fof(f111,plain,(
% 2.91/1.00    m1_subset_1(sK9,u1_struct_0(sK7))),
% 2.91/1.00    inference(cnf_transformation,[],[f64])).
% 2.91/1.00  
% 2.91/1.00  fof(f115,plain,(
% 2.91/1.00    ~r1_tmap_1(sK7,sK5,sK8,sK9)),
% 2.91/1.00    inference(cnf_transformation,[],[f64])).
% 2.91/1.00  
% 2.91/1.00  fof(f112,plain,(
% 2.91/1.00    m1_subset_1(sK10,u1_struct_0(sK6))),
% 2.91/1.00    inference(cnf_transformation,[],[f64])).
% 2.91/1.00  
% 2.91/1.00  cnf(c_13,plain,
% 2.91/1.00      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 2.91/1.00      | ~ v2_pre_topc(X0)
% 2.91/1.00      | ~ l1_pre_topc(X0) ),
% 2.91/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_7125,plain,
% 2.91/1.00      ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
% 2.91/1.00      | ~ v2_pre_topc(sK7)
% 2.91/1.00      | ~ l1_pre_topc(sK7) ),
% 2.91/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_41,negated_conjecture,
% 2.91/1.00      ( m1_pre_topc(sK7,sK4) ),
% 2.91/1.00      inference(cnf_transformation,[],[f106]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3094,plain,
% 2.91/1.00      ( m1_pre_topc(sK7,sK4) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_16,plain,
% 2.91/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.91/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3109,plain,
% 2.91/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 2.91/1.00      | l1_pre_topc(X1) != iProver_top
% 2.91/1.00      | l1_pre_topc(X0) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_4987,plain,
% 2.91/1.00      ( l1_pre_topc(sK4) != iProver_top
% 2.91/1.00      | l1_pre_topc(sK7) = iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_3094,c_3109]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_48,negated_conjecture,
% 2.91/1.00      ( l1_pre_topc(sK4) ),
% 2.91/1.00      inference(cnf_transformation,[],[f99]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_53,plain,
% 2.91/1.00      ( l1_pre_topc(sK4) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_5154,plain,
% 2.91/1.00      ( l1_pre_topc(sK7) = iProver_top ),
% 2.91/1.00      inference(global_propositional_subsumption,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_4987,c_53]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_0,plain,
% 2.91/1.00      ( ~ l1_pre_topc(X0)
% 2.91/1.00      | ~ v1_pre_topc(X0)
% 2.91/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 2.91/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3123,plain,
% 2.91/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 2.91/1.00      | l1_pre_topc(X0) != iProver_top
% 2.91/1.00      | v1_pre_topc(X0) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_5394,plain,
% 2.91/1.00      ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = sK7
% 2.91/1.00      | v1_pre_topc(sK7) != iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_5154,c_3123]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_43,negated_conjecture,
% 2.91/1.00      ( m1_pre_topc(sK6,sK4) ),
% 2.91/1.00      inference(cnf_transformation,[],[f104]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3092,plain,
% 2.91/1.00      ( m1_pre_topc(sK6,sK4) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_4988,plain,
% 2.91/1.00      ( l1_pre_topc(sK4) != iProver_top
% 2.91/1.00      | l1_pre_topc(sK6) = iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_3092,c_3109]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_28,plain,
% 2.91/1.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 2.91/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3101,plain,
% 2.91/1.00      ( m1_pre_topc(X0,X0) = iProver_top
% 2.91/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_37,negated_conjecture,
% 2.91/1.00      ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
% 2.91/1.00      inference(cnf_transformation,[],[f110]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_21,plain,
% 2.91/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.91/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.91/1.00      | ~ l1_pre_topc(X0)
% 2.91/1.00      | ~ l1_pre_topc(X1) ),
% 2.91/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_283,plain,
% 2.91/1.00      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.91/1.00      | ~ m1_pre_topc(X0,X1)
% 2.91/1.00      | ~ l1_pre_topc(X1) ),
% 2.91/1.00      inference(global_propositional_subsumption,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_21,c_16]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_284,plain,
% 2.91/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.91/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.91/1.00      | ~ l1_pre_topc(X1) ),
% 2.91/1.00      inference(renaming,[status(thm)],[c_283]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3084,plain,
% 2.91/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 2.91/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 2.91/1.00      | l1_pre_topc(X1) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_284]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_4152,plain,
% 2.91/1.00      ( m1_pre_topc(X0,sK6) != iProver_top
% 2.91/1.00      | m1_pre_topc(X0,sK7) = iProver_top
% 2.91/1.00      | l1_pre_topc(sK6) != iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_37,c_3084]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_4411,plain,
% 2.91/1.00      ( m1_pre_topc(sK6,sK7) = iProver_top
% 2.91/1.00      | l1_pre_topc(sK6) != iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_3101,c_4152]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_23,plain,
% 2.91/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.91/1.00      | ~ l1_pre_topc(X1)
% 2.91/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.91/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3103,plain,
% 2.91/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 2.91/1.00      | l1_pre_topc(X1) != iProver_top
% 2.91/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_5524,plain,
% 2.91/1.00      ( l1_pre_topc(sK6) != iProver_top
% 2.91/1.00      | l1_pre_topc(sK7) != iProver_top
% 2.91/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_4411,c_3103]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_5528,plain,
% 2.91/1.00      ( l1_pre_topc(sK6) != iProver_top
% 2.91/1.00      | l1_pre_topc(sK7) != iProver_top
% 2.91/1.00      | v1_pre_topc(sK7) = iProver_top ),
% 2.91/1.00      inference(light_normalisation,[status(thm)],[c_5524,c_37]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_5836,plain,
% 2.91/1.00      ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = sK7 ),
% 2.91/1.00      inference(global_propositional_subsumption,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_5394,c_53,c_4987,c_4988,c_5528]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_19,plain,
% 2.91/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.91/1.00      | X2 = X1
% 2.91/1.00      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 2.91/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3106,plain,
% 2.91/1.00      ( X0 = X1
% 2.91/1.00      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 2.91/1.00      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_5965,plain,
% 2.91/1.00      ( g1_pre_topc(X0,X1) != sK7
% 2.91/1.00      | u1_struct_0(sK6) = X0
% 2.91/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_37,c_3106]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_6011,plain,
% 2.91/1.00      ( u1_struct_0(sK7) = u1_struct_0(sK6)
% 2.91/1.00      | m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_5836,c_5965]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_17,plain,
% 2.91/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.91/1.00      | ~ l1_pre_topc(X0) ),
% 2.91/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3716,plain,
% 2.91/1.00      ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
% 2.91/1.00      | ~ l1_pre_topc(sK7) ),
% 2.91/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3721,plain,
% 2.91/1.00      ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top
% 2.91/1.00      | l1_pre_topc(sK7) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_3716]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_6683,plain,
% 2.91/1.00      ( u1_struct_0(sK7) = u1_struct_0(sK6) ),
% 2.91/1.00      inference(global_propositional_subsumption,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_6011,c_53,c_3721,c_4987]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_33,negated_conjecture,
% 2.91/1.00      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
% 2.91/1.00      inference(cnf_transformation,[],[f114]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3098,plain,
% 2.91/1.00      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_34,negated_conjecture,
% 2.91/1.00      ( sK9 = sK10 ),
% 2.91/1.00      inference(cnf_transformation,[],[f113]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3161,plain,
% 2.91/1.00      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9) = iProver_top ),
% 2.91/1.00      inference(light_normalisation,[status(thm)],[c_3098,c_34]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_14,plain,
% 2.91/1.00      ( v3_pre_topc(X0,X1)
% 2.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.91/1.00      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.91/1.00      | ~ l1_pre_topc(X1) ),
% 2.91/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_25,plain,
% 2.91/1.00      ( v1_tsep_1(X0,X1)
% 2.91/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 2.91/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.91/1.00      | ~ m1_pre_topc(X0,X1)
% 2.91/1.00      | ~ v2_pre_topc(X1)
% 2.91/1.00      | ~ l1_pre_topc(X1) ),
% 2.91/1.00      inference(cnf_transformation,[],[f117]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_27,plain,
% 2.91/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.91/1.00      | ~ m1_pre_topc(X0,X1)
% 2.91/1.00      | ~ l1_pre_topc(X1) ),
% 2.91/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_274,plain,
% 2.91/1.00      ( ~ v3_pre_topc(u1_struct_0(X0),X1)
% 2.91/1.00      | v1_tsep_1(X0,X1)
% 2.91/1.00      | ~ m1_pre_topc(X0,X1)
% 2.91/1.00      | ~ v2_pre_topc(X1)
% 2.91/1.00      | ~ l1_pre_topc(X1) ),
% 2.91/1.00      inference(global_propositional_subsumption,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_25,c_27]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_275,plain,
% 2.91/1.00      ( v1_tsep_1(X0,X1)
% 2.91/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 2.91/1.00      | ~ m1_pre_topc(X0,X1)
% 2.91/1.00      | ~ v2_pre_topc(X1)
% 2.91/1.00      | ~ l1_pre_topc(X1) ),
% 2.91/1.00      inference(renaming,[status(thm)],[c_274]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_594,plain,
% 2.91/1.00      ( v1_tsep_1(X0,X1)
% 2.91/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.91/1.00      | ~ r2_hidden(X2,u1_pre_topc(X3))
% 2.91/1.00      | ~ m1_pre_topc(X0,X1)
% 2.91/1.00      | ~ v2_pre_topc(X1)
% 2.91/1.00      | ~ l1_pre_topc(X3)
% 2.91/1.00      | ~ l1_pre_topc(X1)
% 2.91/1.00      | X1 != X3
% 2.91/1.00      | u1_struct_0(X0) != X2 ),
% 2.91/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_275]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_595,plain,
% 2.91/1.00      ( v1_tsep_1(X0,X1)
% 2.91/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.91/1.00      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
% 2.91/1.00      | ~ m1_pre_topc(X0,X1)
% 2.91/1.00      | ~ v2_pre_topc(X1)
% 2.91/1.00      | ~ l1_pre_topc(X1) ),
% 2.91/1.00      inference(unflattening,[status(thm)],[c_594]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_599,plain,
% 2.91/1.00      ( v1_tsep_1(X0,X1)
% 2.91/1.00      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
% 2.91/1.00      | ~ m1_pre_topc(X0,X1)
% 2.91/1.00      | ~ v2_pre_topc(X1)
% 2.91/1.00      | ~ l1_pre_topc(X1) ),
% 2.91/1.00      inference(global_propositional_subsumption,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_595,c_27]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_30,plain,
% 2.91/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.91/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.91/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.91/1.00      | ~ v1_tsep_1(X4,X0)
% 2.91/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.91/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.91/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.91/1.00      | ~ m1_pre_topc(X0,X5)
% 2.91/1.00      | ~ m1_pre_topc(X4,X0)
% 2.91/1.00      | ~ m1_pre_topc(X4,X5)
% 2.91/1.00      | v2_struct_0(X5)
% 2.91/1.00      | v2_struct_0(X1)
% 2.91/1.00      | v2_struct_0(X4)
% 2.91/1.00      | v2_struct_0(X0)
% 2.91/1.00      | ~ v1_funct_1(X2)
% 2.91/1.00      | ~ v2_pre_topc(X5)
% 2.91/1.00      | ~ v2_pre_topc(X1)
% 2.91/1.00      | ~ l1_pre_topc(X5)
% 2.91/1.00      | ~ l1_pre_topc(X1) ),
% 2.91/1.00      inference(cnf_transformation,[],[f119]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_39,negated_conjecture,
% 2.91/1.00      ( v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
% 2.91/1.00      inference(cnf_transformation,[],[f108]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_729,plain,
% 2.91/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.91/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.91/1.00      | ~ v1_tsep_1(X4,X0)
% 2.91/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.91/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.91/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.91/1.00      | ~ m1_pre_topc(X4,X0)
% 2.91/1.00      | ~ m1_pre_topc(X0,X5)
% 2.91/1.00      | ~ m1_pre_topc(X4,X5)
% 2.91/1.00      | v2_struct_0(X0)
% 2.91/1.00      | v2_struct_0(X1)
% 2.91/1.00      | v2_struct_0(X4)
% 2.91/1.00      | v2_struct_0(X5)
% 2.91/1.00      | ~ v1_funct_1(X2)
% 2.91/1.00      | ~ v2_pre_topc(X1)
% 2.91/1.00      | ~ v2_pre_topc(X5)
% 2.91/1.00      | ~ l1_pre_topc(X1)
% 2.91/1.00      | ~ l1_pre_topc(X5)
% 2.91/1.00      | u1_struct_0(X1) != u1_struct_0(sK5)
% 2.91/1.00      | u1_struct_0(X0) != u1_struct_0(sK7)
% 2.91/1.00      | sK8 != X2 ),
% 2.91/1.00      inference(resolution_lifted,[status(thm)],[c_30,c_39]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_730,plain,
% 2.91/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 2.91/1.00      | r1_tmap_1(X3,X1,sK8,X4)
% 2.91/1.00      | ~ v1_tsep_1(X0,X3)
% 2.91/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.91/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.91/1.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.91/1.00      | ~ m1_pre_topc(X0,X3)
% 2.91/1.00      | ~ m1_pre_topc(X3,X2)
% 2.91/1.00      | ~ m1_pre_topc(X0,X2)
% 2.91/1.00      | v2_struct_0(X3)
% 2.91/1.00      | v2_struct_0(X1)
% 2.91/1.00      | v2_struct_0(X0)
% 2.91/1.00      | v2_struct_0(X2)
% 2.91/1.00      | ~ v1_funct_1(sK8)
% 2.91/1.00      | ~ v2_pre_topc(X1)
% 2.91/1.00      | ~ v2_pre_topc(X2)
% 2.91/1.00      | ~ l1_pre_topc(X1)
% 2.91/1.00      | ~ l1_pre_topc(X2)
% 2.91/1.00      | u1_struct_0(X1) != u1_struct_0(sK5)
% 2.91/1.00      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 2.91/1.00      inference(unflattening,[status(thm)],[c_729]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_40,negated_conjecture,
% 2.91/1.00      ( v1_funct_1(sK8) ),
% 2.91/1.00      inference(cnf_transformation,[],[f107]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_734,plain,
% 2.91/1.00      ( v2_struct_0(X2)
% 2.91/1.00      | v2_struct_0(X0)
% 2.91/1.00      | v2_struct_0(X1)
% 2.91/1.00      | v2_struct_0(X3)
% 2.91/1.00      | ~ m1_pre_topc(X0,X2)
% 2.91/1.00      | ~ m1_pre_topc(X3,X2)
% 2.91/1.00      | ~ m1_pre_topc(X0,X3)
% 2.91/1.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.91/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.91/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.91/1.00      | ~ v1_tsep_1(X0,X3)
% 2.91/1.00      | r1_tmap_1(X3,X1,sK8,X4)
% 2.91/1.00      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 2.91/1.00      | ~ v2_pre_topc(X1)
% 2.91/1.00      | ~ v2_pre_topc(X2)
% 2.91/1.00      | ~ l1_pre_topc(X1)
% 2.91/1.00      | ~ l1_pre_topc(X2)
% 2.91/1.00      | u1_struct_0(X1) != u1_struct_0(sK5)
% 2.91/1.00      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 2.91/1.00      inference(global_propositional_subsumption,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_730,c_40]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_735,plain,
% 2.91/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 2.91/1.00      | r1_tmap_1(X3,X1,sK8,X4)
% 2.91/1.00      | ~ v1_tsep_1(X0,X3)
% 2.91/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.91/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.91/1.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.91/1.00      | ~ m1_pre_topc(X0,X3)
% 2.91/1.00      | ~ m1_pre_topc(X3,X2)
% 2.91/1.00      | ~ m1_pre_topc(X0,X2)
% 2.91/1.00      | v2_struct_0(X0)
% 2.91/1.00      | v2_struct_0(X1)
% 2.91/1.00      | v2_struct_0(X2)
% 2.91/1.00      | v2_struct_0(X3)
% 2.91/1.00      | ~ v2_pre_topc(X1)
% 2.91/1.00      | ~ v2_pre_topc(X2)
% 2.91/1.00      | ~ l1_pre_topc(X1)
% 2.91/1.00      | ~ l1_pre_topc(X2)
% 2.91/1.00      | u1_struct_0(X1) != u1_struct_0(sK5)
% 2.91/1.00      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 2.91/1.00      inference(renaming,[status(thm)],[c_734]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_29,plain,
% 2.91/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.91/1.00      | ~ m1_pre_topc(X2,X0)
% 2.91/1.00      | m1_pre_topc(X2,X1)
% 2.91/1.00      | ~ v2_pre_topc(X1)
% 2.91/1.00      | ~ l1_pre_topc(X1) ),
% 2.91/1.00      inference(cnf_transformation,[],[f94]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_778,plain,
% 2.91/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 2.91/1.00      | r1_tmap_1(X3,X1,sK8,X4)
% 2.91/1.00      | ~ v1_tsep_1(X0,X3)
% 2.91/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.91/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.91/1.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.91/1.00      | ~ m1_pre_topc(X0,X3)
% 2.91/1.00      | ~ m1_pre_topc(X3,X2)
% 2.91/1.00      | v2_struct_0(X0)
% 2.91/1.00      | v2_struct_0(X1)
% 2.91/1.00      | v2_struct_0(X2)
% 2.91/1.00      | v2_struct_0(X3)
% 2.91/1.00      | ~ v2_pre_topc(X1)
% 2.91/1.00      | ~ v2_pre_topc(X2)
% 2.91/1.00      | ~ l1_pre_topc(X1)
% 2.91/1.00      | ~ l1_pre_topc(X2)
% 2.91/1.00      | u1_struct_0(X1) != u1_struct_0(sK5)
% 2.91/1.00      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 2.91/1.00      inference(forward_subsumption_resolution,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_735,c_29]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_801,plain,
% 2.91/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 2.91/1.00      | r1_tmap_1(X3,X1,sK8,X4)
% 2.91/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.91/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.91/1.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.91/1.00      | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X6))
% 2.91/1.00      | ~ m1_pre_topc(X5,X6)
% 2.91/1.00      | ~ m1_pre_topc(X0,X3)
% 2.91/1.00      | ~ m1_pre_topc(X3,X2)
% 2.91/1.00      | v2_struct_0(X1)
% 2.91/1.00      | v2_struct_0(X0)
% 2.91/1.00      | v2_struct_0(X2)
% 2.91/1.00      | v2_struct_0(X3)
% 2.91/1.00      | ~ v2_pre_topc(X6)
% 2.91/1.00      | ~ v2_pre_topc(X2)
% 2.91/1.00      | ~ v2_pre_topc(X1)
% 2.91/1.00      | ~ l1_pre_topc(X6)
% 2.91/1.00      | ~ l1_pre_topc(X2)
% 2.91/1.00      | ~ l1_pre_topc(X1)
% 2.91/1.00      | X0 != X5
% 2.91/1.00      | X3 != X6
% 2.91/1.00      | u1_struct_0(X1) != u1_struct_0(sK5)
% 2.91/1.00      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 2.91/1.00      inference(resolution_lifted,[status(thm)],[c_599,c_778]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_802,plain,
% 2.91/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 2.91/1.00      | r1_tmap_1(X3,X1,sK8,X4)
% 2.91/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.91/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.91/1.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.91/1.00      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X3))
% 2.91/1.00      | ~ m1_pre_topc(X0,X3)
% 2.91/1.00      | ~ m1_pre_topc(X3,X2)
% 2.91/1.00      | v2_struct_0(X1)
% 2.91/1.00      | v2_struct_0(X2)
% 2.91/1.00      | v2_struct_0(X0)
% 2.91/1.00      | v2_struct_0(X3)
% 2.91/1.00      | ~ v2_pre_topc(X1)
% 2.91/1.00      | ~ v2_pre_topc(X2)
% 2.91/1.00      | ~ v2_pre_topc(X3)
% 2.91/1.00      | ~ l1_pre_topc(X1)
% 2.91/1.00      | ~ l1_pre_topc(X2)
% 2.91/1.00      | ~ l1_pre_topc(X3)
% 2.91/1.00      | u1_struct_0(X1) != u1_struct_0(sK5)
% 2.91/1.00      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 2.91/1.00      inference(unflattening,[status(thm)],[c_801]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_1,plain,
% 2.91/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.91/1.00      | ~ v2_pre_topc(X1)
% 2.91/1.00      | v2_pre_topc(X0)
% 2.91/1.00      | ~ l1_pre_topc(X1) ),
% 2.91/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_846,plain,
% 2.91/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 2.91/1.00      | r1_tmap_1(X3,X1,sK8,X4)
% 2.91/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.91/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.91/1.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.91/1.00      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X3))
% 2.91/1.00      | ~ m1_pre_topc(X0,X3)
% 2.91/1.00      | ~ m1_pre_topc(X3,X2)
% 2.91/1.00      | v2_struct_0(X0)
% 2.91/1.00      | v2_struct_0(X1)
% 2.91/1.00      | v2_struct_0(X2)
% 2.91/1.00      | v2_struct_0(X3)
% 2.91/1.00      | ~ v2_pre_topc(X1)
% 2.91/1.00      | ~ v2_pre_topc(X2)
% 2.91/1.00      | ~ l1_pre_topc(X1)
% 2.91/1.00      | ~ l1_pre_topc(X2)
% 2.91/1.00      | u1_struct_0(X1) != u1_struct_0(sK5)
% 2.91/1.00      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 2.91/1.00      inference(forward_subsumption_resolution,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_802,c_16,c_1]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3083,plain,
% 2.91/1.00      ( u1_struct_0(X0) != u1_struct_0(sK5)
% 2.91/1.00      | u1_struct_0(X1) != u1_struct_0(sK7)
% 2.91/1.00      | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK8),X4) != iProver_top
% 2.91/1.00      | r1_tmap_1(X1,X0,sK8,X4) = iProver_top
% 2.91/1.00      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 2.91/1.00      | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
% 2.91/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 2.91/1.00      | r2_hidden(u1_struct_0(X2),u1_pre_topc(X1)) != iProver_top
% 2.91/1.00      | m1_pre_topc(X2,X1) != iProver_top
% 2.91/1.00      | m1_pre_topc(X1,X3) != iProver_top
% 2.91/1.00      | v2_struct_0(X0) = iProver_top
% 2.91/1.00      | v2_struct_0(X2) = iProver_top
% 2.91/1.00      | v2_struct_0(X1) = iProver_top
% 2.91/1.00      | v2_struct_0(X3) = iProver_top
% 2.91/1.00      | v2_pre_topc(X0) != iProver_top
% 2.91/1.00      | v2_pre_topc(X3) != iProver_top
% 2.91/1.00      | l1_pre_topc(X0) != iProver_top
% 2.91/1.00      | l1_pre_topc(X3) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_846]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_4050,plain,
% 2.91/1.00      ( u1_struct_0(X0) != u1_struct_0(sK7)
% 2.91/1.00      | r1_tmap_1(X1,sK5,k3_tmap_1(X2,sK5,X0,X1,sK8),X3) != iProver_top
% 2.91/1.00      | r1_tmap_1(X0,sK5,sK8,X3) = iProver_top
% 2.91/1.00      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.91/1.00      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.91/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 2.91/1.00      | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) != iProver_top
% 2.91/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 2.91/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 2.91/1.00      | v2_struct_0(X1) = iProver_top
% 2.91/1.00      | v2_struct_0(X0) = iProver_top
% 2.91/1.00      | v2_struct_0(X2) = iProver_top
% 2.91/1.00      | v2_struct_0(sK5) = iProver_top
% 2.91/1.00      | v2_pre_topc(X2) != iProver_top
% 2.91/1.00      | v2_pre_topc(sK5) != iProver_top
% 2.91/1.00      | l1_pre_topc(X2) != iProver_top
% 2.91/1.00      | l1_pre_topc(sK5) != iProver_top ),
% 2.91/1.00      inference(equality_resolution,[status(thm)],[c_3083]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_47,negated_conjecture,
% 2.91/1.00      ( ~ v2_struct_0(sK5) ),
% 2.91/1.00      inference(cnf_transformation,[],[f100]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_54,plain,
% 2.91/1.00      ( v2_struct_0(sK5) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_46,negated_conjecture,
% 2.91/1.00      ( v2_pre_topc(sK5) ),
% 2.91/1.00      inference(cnf_transformation,[],[f101]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_55,plain,
% 2.91/1.00      ( v2_pre_topc(sK5) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_45,negated_conjecture,
% 2.91/1.00      ( l1_pre_topc(sK5) ),
% 2.91/1.00      inference(cnf_transformation,[],[f102]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_56,plain,
% 2.91/1.00      ( l1_pre_topc(sK5) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_4126,plain,
% 2.91/1.00      ( l1_pre_topc(X2) != iProver_top
% 2.91/1.00      | v2_struct_0(X2) = iProver_top
% 2.91/1.00      | v2_struct_0(X0) = iProver_top
% 2.91/1.00      | v2_struct_0(X1) = iProver_top
% 2.91/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 2.91/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 2.91/1.00      | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) != iProver_top
% 2.91/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 2.91/1.00      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.91/1.00      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.91/1.00      | r1_tmap_1(X0,sK5,sK8,X3) = iProver_top
% 2.91/1.00      | r1_tmap_1(X1,sK5,k3_tmap_1(X2,sK5,X0,X1,sK8),X3) != iProver_top
% 2.91/1.00      | u1_struct_0(X0) != u1_struct_0(sK7)
% 2.91/1.00      | v2_pre_topc(X2) != iProver_top ),
% 2.91/1.00      inference(global_propositional_subsumption,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_4050,c_54,c_55,c_56]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_4127,plain,
% 2.91/1.00      ( u1_struct_0(X0) != u1_struct_0(sK7)
% 2.91/1.00      | r1_tmap_1(X1,sK5,k3_tmap_1(X2,sK5,X0,X1,sK8),X3) != iProver_top
% 2.91/1.00      | r1_tmap_1(X0,sK5,sK8,X3) = iProver_top
% 2.91/1.00      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.91/1.00      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.91/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 2.91/1.00      | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) != iProver_top
% 2.91/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 2.91/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 2.91/1.00      | v2_struct_0(X1) = iProver_top
% 2.91/1.00      | v2_struct_0(X0) = iProver_top
% 2.91/1.00      | v2_struct_0(X2) = iProver_top
% 2.91/1.00      | v2_pre_topc(X2) != iProver_top
% 2.91/1.00      | l1_pre_topc(X2) != iProver_top ),
% 2.91/1.00      inference(renaming,[status(thm)],[c_4126]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_4144,plain,
% 2.91/1.00      ( r1_tmap_1(X0,sK5,k3_tmap_1(X1,sK5,sK7,X0,sK8),X2) != iProver_top
% 2.91/1.00      | r1_tmap_1(sK7,sK5,sK8,X2) = iProver_top
% 2.91/1.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.91/1.00      | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
% 2.91/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
% 2.91/1.00      | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
% 2.91/1.00      | m1_pre_topc(X0,sK7) != iProver_top
% 2.91/1.00      | m1_pre_topc(sK7,X1) != iProver_top
% 2.91/1.00      | v2_struct_0(X1) = iProver_top
% 2.91/1.00      | v2_struct_0(X0) = iProver_top
% 2.91/1.00      | v2_struct_0(sK7) = iProver_top
% 2.91/1.00      | v2_pre_topc(X1) != iProver_top
% 2.91/1.00      | l1_pre_topc(X1) != iProver_top ),
% 2.91/1.00      inference(equality_resolution,[status(thm)],[c_4127]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_42,negated_conjecture,
% 2.91/1.00      ( ~ v2_struct_0(sK7) ),
% 2.91/1.00      inference(cnf_transformation,[],[f105]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_59,plain,
% 2.91/1.00      ( v2_struct_0(sK7) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_38,negated_conjecture,
% 2.91/1.00      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
% 2.91/1.00      inference(cnf_transformation,[],[f109]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_63,plain,
% 2.91/1.00      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_4531,plain,
% 2.91/1.00      ( v2_struct_0(X0) = iProver_top
% 2.91/1.00      | v2_struct_0(X1) = iProver_top
% 2.91/1.00      | m1_pre_topc(sK7,X1) != iProver_top
% 2.91/1.00      | m1_pre_topc(X0,sK7) != iProver_top
% 2.91/1.00      | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
% 2.91/1.00      | r1_tmap_1(X0,sK5,k3_tmap_1(X1,sK5,sK7,X0,sK8),X2) != iProver_top
% 2.91/1.00      | r1_tmap_1(sK7,sK5,sK8,X2) = iProver_top
% 2.91/1.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.91/1.00      | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
% 2.91/1.00      | v2_pre_topc(X1) != iProver_top
% 2.91/1.00      | l1_pre_topc(X1) != iProver_top ),
% 2.91/1.00      inference(global_propositional_subsumption,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_4144,c_59,c_63]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_4532,plain,
% 2.91/1.00      ( r1_tmap_1(X0,sK5,k3_tmap_1(X1,sK5,sK7,X0,sK8),X2) != iProver_top
% 2.91/1.00      | r1_tmap_1(sK7,sK5,sK8,X2) = iProver_top
% 2.91/1.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.91/1.00      | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
% 2.91/1.00      | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
% 2.91/1.00      | m1_pre_topc(X0,sK7) != iProver_top
% 2.91/1.00      | m1_pre_topc(sK7,X1) != iProver_top
% 2.91/1.00      | v2_struct_0(X1) = iProver_top
% 2.91/1.00      | v2_struct_0(X0) = iProver_top
% 2.91/1.00      | v2_pre_topc(X1) != iProver_top
% 2.91/1.00      | l1_pre_topc(X1) != iProver_top ),
% 2.91/1.00      inference(renaming,[status(thm)],[c_4531]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_4548,plain,
% 2.91/1.00      ( r1_tmap_1(sK7,sK5,sK8,sK9) = iProver_top
% 2.91/1.00      | m1_subset_1(sK9,u1_struct_0(sK6)) != iProver_top
% 2.91/1.00      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 2.91/1.00      | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top
% 2.91/1.00      | m1_pre_topc(sK6,sK7) != iProver_top
% 2.91/1.00      | m1_pre_topc(sK7,sK4) != iProver_top
% 2.91/1.00      | v2_struct_0(sK4) = iProver_top
% 2.91/1.00      | v2_struct_0(sK6) = iProver_top
% 2.91/1.00      | v2_pre_topc(sK4) != iProver_top
% 2.91/1.00      | l1_pre_topc(sK4) != iProver_top ),
% 2.91/1.00      inference(superposition,[status(thm)],[c_3161,c_4532]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_50,negated_conjecture,
% 2.91/1.00      ( ~ v2_struct_0(sK4) ),
% 2.91/1.00      inference(cnf_transformation,[],[f97]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_51,plain,
% 2.91/1.00      ( v2_struct_0(sK4) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_49,negated_conjecture,
% 2.91/1.00      ( v2_pre_topc(sK4) ),
% 2.91/1.00      inference(cnf_transformation,[],[f98]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_52,plain,
% 2.91/1.00      ( v2_pre_topc(sK4) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_44,negated_conjecture,
% 2.91/1.00      ( ~ v2_struct_0(sK6) ),
% 2.91/1.00      inference(cnf_transformation,[],[f103]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_57,plain,
% 2.91/1.00      ( v2_struct_0(sK6) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_60,plain,
% 2.91/1.00      ( m1_pre_topc(sK7,sK4) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_36,negated_conjecture,
% 2.91/1.00      ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
% 2.91/1.00      inference(cnf_transformation,[],[f111]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_64,plain,
% 2.91/1.00      ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_32,negated_conjecture,
% 2.91/1.00      ( ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
% 2.91/1.00      inference(cnf_transformation,[],[f115]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_67,plain,
% 2.91/1.00      ( r1_tmap_1(sK7,sK5,sK8,sK9) != iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_35,negated_conjecture,
% 2.91/1.00      ( m1_subset_1(sK10,u1_struct_0(sK6)) ),
% 2.91/1.00      inference(cnf_transformation,[],[f112]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3097,plain,
% 2.91/1.00      ( m1_subset_1(sK10,u1_struct_0(sK6)) = iProver_top ),
% 2.91/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_3148,plain,
% 2.91/1.00      ( m1_subset_1(sK9,u1_struct_0(sK6)) = iProver_top ),
% 2.91/1.00      inference(light_normalisation,[status(thm)],[c_3097,c_34]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_4653,plain,
% 2.91/1.00      ( m1_pre_topc(sK6,sK7) != iProver_top
% 2.91/1.00      | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top ),
% 2.91/1.00      inference(global_propositional_subsumption,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_4548,c_51,c_52,c_53,c_57,c_60,c_64,c_67,c_3148]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_4654,plain,
% 2.91/1.00      ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top
% 2.91/1.00      | m1_pre_topc(sK6,sK7) != iProver_top ),
% 2.91/1.00      inference(renaming,[status(thm)],[c_4653]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_6689,plain,
% 2.91/1.00      ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) != iProver_top
% 2.91/1.00      | m1_pre_topc(sK6,sK7) != iProver_top ),
% 2.91/1.00      inference(demodulation,[status(thm)],[c_6683,c_4654]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_6716,plain,
% 2.91/1.00      ( ~ r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
% 2.91/1.00      | ~ m1_pre_topc(sK6,sK7) ),
% 2.91/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6689]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_4159,plain,
% 2.91/1.00      ( ~ m1_pre_topc(sK7,X0)
% 2.91/1.00      | ~ v2_pre_topc(X0)
% 2.91/1.00      | v2_pre_topc(sK7)
% 2.91/1.00      | ~ l1_pre_topc(X0) ),
% 2.91/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_5300,plain,
% 2.91/1.00      ( ~ m1_pre_topc(sK7,sK4)
% 2.91/1.00      | ~ v2_pre_topc(sK4)
% 2.91/1.00      | v2_pre_topc(sK7)
% 2.91/1.00      | ~ l1_pre_topc(sK4) ),
% 2.91/1.00      inference(instantiation,[status(thm)],[c_4159]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_4999,plain,
% 2.91/1.00      ( ~ l1_pre_topc(sK4) | l1_pre_topc(sK6) ),
% 2.91/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4988]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_4998,plain,
% 2.91/1.00      ( ~ l1_pre_topc(sK4) | l1_pre_topc(sK7) ),
% 2.91/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4987]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(c_4412,plain,
% 2.91/1.00      ( m1_pre_topc(sK6,sK7) | ~ l1_pre_topc(sK6) ),
% 2.91/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4411]) ).
% 2.91/1.00  
% 2.91/1.00  cnf(contradiction,plain,
% 2.91/1.00      ( $false ),
% 2.91/1.00      inference(minisat,
% 2.91/1.00                [status(thm)],
% 2.91/1.00                [c_7125,c_6716,c_5300,c_4999,c_4998,c_4412,c_41,c_48,
% 2.91/1.00                 c_49]) ).
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.91/1.00  
% 2.91/1.00  ------                               Statistics
% 2.91/1.00  
% 2.91/1.00  ------ General
% 2.91/1.00  
% 2.91/1.00  abstr_ref_over_cycles:                  0
% 2.91/1.00  abstr_ref_under_cycles:                 0
% 2.91/1.00  gc_basic_clause_elim:                   0
% 2.91/1.00  forced_gc_time:                         0
% 2.91/1.00  parsing_time:                           0.012
% 2.91/1.00  unif_index_cands_time:                  0.
% 2.91/1.00  unif_index_add_time:                    0.
% 2.91/1.00  orderings_time:                         0.
% 2.91/1.00  out_proof_time:                         0.012
% 2.91/1.00  total_time:                             0.212
% 2.91/1.00  num_of_symbols:                         63
% 2.91/1.00  num_of_terms:                           5552
% 2.91/1.00  
% 2.91/1.00  ------ Preprocessing
% 2.91/1.00  
% 2.91/1.00  num_of_splits:                          0
% 2.91/1.00  num_of_split_atoms:                     0
% 2.91/1.00  num_of_reused_defs:                     0
% 2.91/1.00  num_eq_ax_congr_red:                    15
% 2.91/1.00  num_of_sem_filtered_clauses:            1
% 2.91/1.00  num_of_subtypes:                        0
% 2.91/1.00  monotx_restored_types:                  0
% 2.91/1.00  sat_num_of_epr_types:                   0
% 2.91/1.00  sat_num_of_non_cyclic_types:            0
% 2.91/1.00  sat_guarded_non_collapsed_types:        0
% 2.91/1.00  num_pure_diseq_elim:                    0
% 2.91/1.00  simp_replaced_by:                       0
% 2.91/1.00  res_preprocessed:                       221
% 2.91/1.00  prep_upred:                             0
% 2.91/1.00  prep_unflattend:                        26
% 2.91/1.00  smt_new_axioms:                         0
% 2.91/1.00  pred_elim_cands:                        10
% 2.91/1.00  pred_elim:                              4
% 2.91/1.00  pred_elim_cl:                           6
% 2.91/1.00  pred_elim_cycles:                       10
% 2.91/1.00  merged_defs:                            0
% 2.91/1.00  merged_defs_ncl:                        0
% 2.91/1.00  bin_hyper_res:                          0
% 2.91/1.00  prep_cycles:                            4
% 2.91/1.00  pred_elim_time:                         0.034
% 2.91/1.00  splitting_time:                         0.
% 2.91/1.00  sem_filter_time:                        0.
% 2.91/1.00  monotx_time:                            0.001
% 2.91/1.00  subtype_inf_time:                       0.
% 2.91/1.00  
% 2.91/1.00  ------ Problem properties
% 2.91/1.00  
% 2.91/1.00  clauses:                                44
% 2.91/1.00  conjectures:                            17
% 2.91/1.00  epr:                                    17
% 2.91/1.00  horn:                                   36
% 2.91/1.00  ground:                                 17
% 2.91/1.00  unary:                                  17
% 2.91/1.00  binary:                                 7
% 2.91/1.00  lits:                                   136
% 2.91/1.00  lits_eq:                                11
% 2.91/1.00  fd_pure:                                0
% 2.91/1.00  fd_pseudo:                              0
% 2.91/1.00  fd_cond:                                0
% 2.91/1.00  fd_pseudo_cond:                         2
% 2.91/1.00  ac_symbols:                             0
% 2.91/1.00  
% 2.91/1.00  ------ Propositional Solver
% 2.91/1.00  
% 2.91/1.00  prop_solver_calls:                      27
% 2.91/1.00  prop_fast_solver_calls:                 2103
% 2.91/1.00  smt_solver_calls:                       0
% 2.91/1.00  smt_fast_solver_calls:                  0
% 2.91/1.00  prop_num_of_clauses:                    1782
% 2.91/1.00  prop_preprocess_simplified:             7647
% 2.91/1.00  prop_fo_subsumed:                       43
% 2.91/1.00  prop_solver_time:                       0.
% 2.91/1.00  smt_solver_time:                        0.
% 2.91/1.00  smt_fast_solver_time:                   0.
% 2.91/1.00  prop_fast_solver_time:                  0.
% 2.91/1.00  prop_unsat_core_time:                   0.
% 2.91/1.00  
% 2.91/1.00  ------ QBF
% 2.91/1.00  
% 2.91/1.00  qbf_q_res:                              0
% 2.91/1.00  qbf_num_tautologies:                    0
% 2.91/1.00  qbf_prep_cycles:                        0
% 2.91/1.00  
% 2.91/1.00  ------ BMC1
% 2.91/1.00  
% 2.91/1.00  bmc1_current_bound:                     -1
% 2.91/1.00  bmc1_last_solved_bound:                 -1
% 2.91/1.00  bmc1_unsat_core_size:                   -1
% 2.91/1.00  bmc1_unsat_core_parents_size:           -1
% 2.91/1.00  bmc1_merge_next_fun:                    0
% 2.91/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.91/1.00  
% 2.91/1.00  ------ Instantiation
% 2.91/1.00  
% 2.91/1.00  inst_num_of_clauses:                    499
% 2.91/1.00  inst_num_in_passive:                    62
% 2.91/1.00  inst_num_in_active:                     337
% 2.91/1.00  inst_num_in_unprocessed:                99
% 2.91/1.00  inst_num_of_loops:                      352
% 2.91/1.00  inst_num_of_learning_restarts:          0
% 2.91/1.00  inst_num_moves_active_passive:          10
% 2.91/1.00  inst_lit_activity:                      0
% 2.91/1.00  inst_lit_activity_moves:                0
% 2.91/1.00  inst_num_tautologies:                   0
% 2.91/1.00  inst_num_prop_implied:                  0
% 2.91/1.00  inst_num_existing_simplified:           0
% 2.91/1.00  inst_num_eq_res_simplified:             0
% 2.91/1.00  inst_num_child_elim:                    0
% 2.91/1.00  inst_num_of_dismatching_blockings:      280
% 2.91/1.00  inst_num_of_non_proper_insts:           781
% 2.91/1.00  inst_num_of_duplicates:                 0
% 2.91/1.00  inst_inst_num_from_inst_to_res:         0
% 2.91/1.00  inst_dismatching_checking_time:         0.
% 2.91/1.00  
% 2.91/1.00  ------ Resolution
% 2.91/1.00  
% 2.91/1.00  res_num_of_clauses:                     0
% 2.91/1.00  res_num_in_passive:                     0
% 2.91/1.00  res_num_in_active:                      0
% 2.91/1.00  res_num_of_loops:                       225
% 2.91/1.00  res_forward_subset_subsumed:            61
% 2.91/1.00  res_backward_subset_subsumed:           2
% 2.91/1.00  res_forward_subsumed:                   0
% 2.91/1.00  res_backward_subsumed:                  0
% 2.91/1.00  res_forward_subsumption_resolution:     6
% 2.91/1.00  res_backward_subsumption_resolution:    0
% 2.91/1.00  res_clause_to_clause_subsumption:       418
% 2.91/1.00  res_orphan_elimination:                 0
% 2.91/1.00  res_tautology_del:                      97
% 2.91/1.00  res_num_eq_res_simplified:              0
% 2.91/1.00  res_num_sel_changes:                    0
% 2.91/1.00  res_moves_from_active_to_pass:          0
% 2.91/1.00  
% 2.91/1.00  ------ Superposition
% 2.91/1.00  
% 2.91/1.00  sup_time_total:                         0.
% 2.91/1.00  sup_time_generating:                    0.
% 2.91/1.00  sup_time_sim_full:                      0.
% 2.91/1.00  sup_time_sim_immed:                     0.
% 2.91/1.00  
% 2.91/1.00  sup_num_of_clauses:                     106
% 2.91/1.00  sup_num_in_active:                      61
% 2.91/1.00  sup_num_in_passive:                     45
% 2.91/1.00  sup_num_of_loops:                       70
% 2.91/1.00  sup_fw_superposition:                   58
% 2.91/1.00  sup_bw_superposition:                   45
% 2.91/1.00  sup_immediate_simplified:               27
% 2.91/1.00  sup_given_eliminated:                   0
% 2.91/1.00  comparisons_done:                       0
% 2.91/1.00  comparisons_avoided:                    0
% 2.91/1.00  
% 2.91/1.00  ------ Simplifications
% 2.91/1.00  
% 2.91/1.00  
% 2.91/1.00  sim_fw_subset_subsumed:                 7
% 2.91/1.00  sim_bw_subset_subsumed:                 2
% 2.91/1.00  sim_fw_subsumed:                        3
% 2.91/1.00  sim_bw_subsumed:                        0
% 2.91/1.00  sim_fw_subsumption_res:                 0
% 2.91/1.00  sim_bw_subsumption_res:                 0
% 2.91/1.00  sim_tautology_del:                      10
% 2.91/1.00  sim_eq_tautology_del:                   7
% 2.91/1.00  sim_eq_res_simp:                        0
% 2.91/1.00  sim_fw_demodulated:                     0
% 2.91/1.00  sim_bw_demodulated:                     9
% 2.91/1.00  sim_light_normalised:                   19
% 2.91/1.00  sim_joinable_taut:                      0
% 2.91/1.00  sim_joinable_simp:                      0
% 2.91/1.00  sim_ac_normalised:                      0
% 2.91/1.00  sim_smt_subsumption:                    0
% 2.91/1.00  
%------------------------------------------------------------------------------
