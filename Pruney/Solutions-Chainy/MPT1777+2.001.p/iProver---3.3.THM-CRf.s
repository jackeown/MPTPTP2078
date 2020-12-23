%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:24 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  251 (1362 expanded)
%              Number of clauses        :  146 ( 312 expanded)
%              Number of leaves         :   28 ( 586 expanded)
%              Depth                    :   32
%              Number of atoms          : 1521 (18938 expanded)
%              Number of equality atoms :  425 (2834 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    5 (   1 average)

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

fof(f24,plain,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f56,plain,(
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

fof(f57,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f30,f56])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f57])).

fof(f67,plain,(
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
    inference(flattening,[],[f66])).

fof(f68,plain,(
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
    inference(rectify,[],[f67])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f68,f69])).

fof(f98,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f22,conjecture,(
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

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f83,plain,(
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

fof(f82,plain,(
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

fof(f81,plain,(
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

fof(f80,plain,(
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

fof(f79,plain,(
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

fof(f78,plain,(
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

fof(f77,plain,
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

fof(f84,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f55,f83,f82,f81,f80,f79,f78,f77])).

fof(f135,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f84])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f116,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f141,plain,(
    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
    inference(cnf_transformation,[],[f84])).

fof(f130,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f84])).

fof(f137,plain,(
    m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f84])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f106,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f122,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f112,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f90,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f107,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f115,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f139,plain,(
    v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f84])).

fof(f138,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f84])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f131,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f84])).

fof(f132,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f84])).

fof(f133,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f84])).

fof(f140,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f84])).

fof(f128,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f84])).

fof(f129,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f84])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f136,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f84])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f145,plain,(
    r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
    inference(cnf_transformation,[],[f84])).

fof(f144,plain,(
    sK9 = sK10 ),
    inference(cnf_transformation,[],[f84])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f16,axiom,(
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

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f73,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f74,plain,(
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
    inference(flattening,[],[f73])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f150,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f119])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f121,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r1_tmap_1(X1,X0,X2,X4)
                              | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | ~ r1_tmap_1(X1,X0,X2,X4) ) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f126,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X4)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_tsep_1(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f152,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_tsep_1(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f126])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f134,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f84])).

fof(f146,plain,(
    ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
    inference(cnf_transformation,[],[f84])).

fof(f143,plain,(
    m1_subset_1(sK10,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_18,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_9570,plain,
    ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_54,negated_conjecture,
    ( m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_3884,plain,
    ( m1_pre_topc(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_32,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_3897,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_8337,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3884,c_3897])).

cnf(c_48,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
    inference(cnf_transformation,[],[f141])).

cnf(c_8348,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | v1_pre_topc(sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8337,c_48])).

cnf(c_59,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_64,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_52,negated_conjecture,
    ( m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_3886,plain,
    ( m1_pre_topc(sK7,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3904,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6892,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3886,c_3904])).

cnf(c_6893,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3884,c_3904])).

cnf(c_37,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_3895,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_28,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_345,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_21])).

cnf(c_346,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_345])).

cnf(c_3876,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_5938,plain,
    ( m1_pre_topc(X0,sK6) != iProver_top
    | m1_pre_topc(X0,sK7) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_48,c_3876])).

cnf(c_6313,plain,
    ( m1_pre_topc(sK6,sK7) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3895,c_5938])).

cnf(c_8338,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6313,c_3897])).

cnf(c_8342,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v1_pre_topc(sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8338,c_48])).

cnf(c_8436,plain,
    ( v1_pre_topc(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8348,c_64,c_6892,c_6893,c_8342])).

cnf(c_7044,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6892,c_64])).

cnf(c_5,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3918,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7665,plain,
    ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = sK7
    | v1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_7044,c_3918])).

cnf(c_8441,plain,
    ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = sK7 ),
    inference(superposition,[status(thm)],[c_8436,c_7665])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_3901,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_8451,plain,
    ( g1_pre_topc(X0,X1) != sK7
    | u1_struct_0(sK6) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_48,c_3901])).

cnf(c_22,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_6299,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_6304,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6299])).

cnf(c_8452,plain,
    ( g1_pre_topc(X0,X1) != sK7
    | u1_struct_0(sK6) = X0
    | m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_48,c_3901])).

cnf(c_8721,plain,
    ( u1_struct_0(sK6) = X0
    | g1_pre_topc(X0,X1) != sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8451,c_64,c_6304,c_6893,c_8452])).

cnf(c_8722,plain,
    ( g1_pre_topc(X0,X1) != sK7
    | u1_struct_0(sK6) = X0 ),
    inference(renaming,[status(thm)],[c_8721])).

cnf(c_8728,plain,
    ( u1_struct_0(sK7) = u1_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_8441,c_8722])).

cnf(c_7133,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6893,c_64])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_50,negated_conjecture,
    ( v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_961,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
    | u1_struct_0(X4) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | sK8 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_50])).

cnf(c_962,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v1_funct_1(sK8)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_961])).

cnf(c_51,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_966,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_962,c_51])).

cnf(c_967,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(renaming,[status(thm)],[c_966])).

cnf(c_42,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_998,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_967,c_42])).

cnf(c_3875,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK8,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK8)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_998])).

cnf(c_5186,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k3_tmap_1(X2,sK5,X0,X1,sK8)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3875])).

cnf(c_58,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_65,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_57,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_66,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_56,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_67,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_5670,plain,
    ( l1_pre_topc(X2) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k3_tmap_1(X2,sK5,X0,X1,sK8)
    | v2_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5186,c_65,c_66,c_67])).

cnf(c_5671,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k3_tmap_1(X2,sK5,X0,X1,sK8)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5670])).

cnf(c_5682,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK5,sK7,X0,sK8)
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_pre_topc(sK7,X1) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5671])).

cnf(c_49,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_74,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_6508,plain,
    ( m1_pre_topc(sK7,X1) != iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK5,sK7,X0,sK8)
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5682,c_74])).

cnf(c_6509,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK5,sK7,X0,sK8)
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_pre_topc(sK7,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6508])).

cnf(c_6521,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(X0,sK5,sK7,sK6,sK8)
    | m1_pre_topc(sK7,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6313,c_6509])).

cnf(c_6561,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(sK4,sK5,sK7,sK6,sK8)
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3886,c_6521])).

cnf(c_61,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_62,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_60,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_63,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_6652,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(sK4,sK5,sK7,sK6,sK8)
    | l1_pre_topc(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6561,c_62,c_63,c_64])).

cnf(c_7139,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(sK4,sK5,sK7,sK6,sK8) ),
    inference(superposition,[status(thm)],[c_7133,c_6652])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1012,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_50])).

cnf(c_1013,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(sK8)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK8,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK8,X0)
    | u1_struct_0(X2) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_1012])).

cnf(c_1017,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK8,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK8,X0)
    | u1_struct_0(X2) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1013,c_51])).

cnf(c_1018,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK8,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK8,X0)
    | u1_struct_0(X2) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(renaming,[status(thm)],[c_1017])).

cnf(c_3874,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK8,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK8,X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1018])).

cnf(c_4995,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k2_tmap_1(X0,sK5,sK8,X1)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3874])).

cnf(c_5158,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k2_tmap_1(X0,sK5,sK8,X1)
    | v2_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4995,c_65,c_66,c_67])).

cnf(c_5159,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k2_tmap_1(X0,sK5,sK8,X1)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5158])).

cnf(c_5169,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k2_tmap_1(sK7,sK5,sK8,X0)
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5159])).

cnf(c_53,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_70,plain,
    ( v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_71,plain,
    ( m1_pre_topc(sK7,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_4767,plain,
    ( ~ m1_pre_topc(sK7,X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK7)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5487,plain,
    ( ~ m1_pre_topc(sK7,sK4)
    | ~ v2_pre_topc(sK4)
    | v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_4767])).

cnf(c_5488,plain,
    ( m1_pre_topc(sK7,sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK7) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5487])).

cnf(c_5658,plain,
    ( m1_pre_topc(X0,sK7) != iProver_top
    | k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k2_tmap_1(sK7,sK5,sK8,X0)
    | l1_pre_topc(sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5169,c_63,c_64,c_70,c_71,c_74,c_5488])).

cnf(c_5659,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k2_tmap_1(sK7,sK5,sK8,X0)
    | m1_pre_topc(X0,sK7) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_5658])).

cnf(c_6416,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k2_tmap_1(sK7,sK5,sK8,sK6)
    | l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_6313,c_5659])).

cnf(c_7140,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k2_tmap_1(sK7,sK5,sK8,sK6)
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_7133,c_6416])).

cnf(c_7146,plain,
    ( k3_tmap_1(sK4,sK5,sK7,sK6,sK8) = k2_tmap_1(sK7,sK5,sK8,sK6)
    | l1_pre_topc(sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7139,c_7140])).

cnf(c_8048,plain,
    ( k3_tmap_1(sK4,sK5,sK7,sK6,sK8) = k2_tmap_1(sK7,sK5,sK8,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7146,c_64,c_6892])).

cnf(c_44,negated_conjecture,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_3890,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_45,negated_conjecture,
    ( sK9 = sK10 ),
    inference(cnf_transformation,[],[f144])).

cnf(c_3962,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3890,c_45])).

cnf(c_8052,plain,
    ( r1_tmap_1(sK6,sK5,k2_tmap_1(sK7,sK5,sK8,sK6),sK9) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8048,c_3962])).

cnf(c_19,plain,
    ( v3_pre_topc(X0,X1)
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_34,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_36,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_334,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34,c_36])).

cnf(c_335,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_334])).

cnf(c_784,plain,
    ( v1_tsep_1(X0,X1)
    | ~ r2_hidden(X2,u1_pre_topc(X3))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | X1 != X3
    | u1_struct_0(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_335])).

cnf(c_785,plain,
    ( v1_tsep_1(X0,X1)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_784])).

cnf(c_789,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
    | v1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_785,c_36])).

cnf(c_790,plain,
    ( v1_tsep_1(X0,X1)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_789])).

cnf(c_40,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_905,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X6))
    | ~ m1_pre_topc(X5,X6)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | X4 != X5
    | X0 != X6 ),
    inference(resolution_lifted,[status(thm)],[c_790,c_40])).

cnf(c_906,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_905])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_942,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_906,c_25])).

cnf(c_1057,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_942,c_50])).

cnf(c_1058,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK8,X0),X3)
    | r1_tmap_1(X2,X1,sK8,X3)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X2))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK8)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X2) != u1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_1057])).

cnf(c_1062,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X2))
    | r1_tmap_1(X2,X1,sK8,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK8,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X2) != u1_struct_0(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1058,c_51])).

cnf(c_1063,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK8,X0),X3)
    | r1_tmap_1(X2,X1,sK8,X3)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X2))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X2) != u1_struct_0(sK7) ),
    inference(renaming,[status(thm)],[c_1062])).

cnf(c_3873,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK8,X2),X3) != iProver_top
    | r1_tmap_1(X1,X0,sK8,X3) = iProver_top
    | r2_hidden(u1_struct_0(X2),u1_pre_topc(X1)) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1063])).

cnf(c_5015,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK5)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
    | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
    | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X1,sK7) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3873])).

cnf(c_2692,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4398,plain,
    ( u1_struct_0(sK7) = u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_2692])).

cnf(c_4680,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK7,X1,sK8,X0),X2)
    | r1_tmap_1(sK7,X1,sK8,X2)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7))
    | ~ m1_pre_topc(X0,sK7)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK7)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK7)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(sK7) != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1063])).

cnf(c_4681,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK5)
    | u1_struct_0(sK7) != u1_struct_0(sK7)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
    | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
    | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X1,sK7) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4680])).

cnf(c_5537,plain,
    ( v2_pre_topc(X0) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK5)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
    | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
    | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X1,sK7) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5015,c_63,c_64,c_70,c_71,c_4398,c_4681,c_5488])).

cnf(c_5538,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK5)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
    | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
    | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X1,sK7) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_5537])).

cnf(c_5555,plain,
    ( r1_tmap_1(X0,sK5,k2_tmap_1(sK7,sK5,sK8,X0),X1) != iProver_top
    | r1_tmap_1(sK7,sK5,sK8,X1) = iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5538])).

cnf(c_5853,plain,
    ( v2_struct_0(X0) = iProver_top
    | r1_tmap_1(X0,sK5,k2_tmap_1(sK7,sK5,sK8,X0),X1) != iProver_top
    | r1_tmap_1(sK7,sK5,sK8,X1) = iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5555,c_65,c_66,c_67,c_74])).

cnf(c_5854,plain,
    ( r1_tmap_1(X0,sK5,k2_tmap_1(sK7,sK5,sK8,X0),X1) != iProver_top
    | r1_tmap_1(sK7,sK5,sK8,X1) = iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_5853])).

cnf(c_8060,plain,
    ( r1_tmap_1(sK7,sK5,sK8,sK9) = iProver_top
    | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(sK6,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8052,c_5854])).

cnf(c_55,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_68,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_43,negated_conjecture,
    ( ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_78,plain,
    ( r1_tmap_1(sK7,sK5,sK8,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_46,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_3889,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_3949,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3889,c_45])).

cnf(c_8202,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8060,c_64,c_68,c_78,c_3949,c_6313,c_6892,c_6893])).

cnf(c_8807,plain,
    ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8728,c_8202])).

cnf(c_8822,plain,
    ( ~ r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8807])).

cnf(c_6903,plain,
    ( ~ l1_pre_topc(sK4)
    | l1_pre_topc(sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6892])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9570,c_8822,c_6903,c_5487,c_52,c_59,c_60])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:13:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.54/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/0.98  
% 3.54/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.54/0.98  
% 3.54/0.98  ------  iProver source info
% 3.54/0.98  
% 3.54/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.54/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.54/0.98  git: non_committed_changes: false
% 3.54/0.98  git: last_make_outside_of_git: false
% 3.54/0.98  
% 3.54/0.98  ------ 
% 3.54/0.98  
% 3.54/0.98  ------ Input Options
% 3.54/0.98  
% 3.54/0.98  --out_options                           all
% 3.54/0.98  --tptp_safe_out                         true
% 3.54/0.98  --problem_path                          ""
% 3.54/0.98  --include_path                          ""
% 3.54/0.98  --clausifier                            res/vclausify_rel
% 3.54/0.98  --clausifier_options                    --mode clausify
% 3.54/0.98  --stdin                                 false
% 3.54/0.98  --stats_out                             all
% 3.54/0.98  
% 3.54/0.98  ------ General Options
% 3.54/0.98  
% 3.54/0.98  --fof                                   false
% 3.54/0.98  --time_out_real                         305.
% 3.54/0.98  --time_out_virtual                      -1.
% 3.54/0.98  --symbol_type_check                     false
% 3.54/0.98  --clausify_out                          false
% 3.54/0.98  --sig_cnt_out                           false
% 3.54/0.98  --trig_cnt_out                          false
% 3.54/0.98  --trig_cnt_out_tolerance                1.
% 3.54/0.98  --trig_cnt_out_sk_spl                   false
% 3.54/0.98  --abstr_cl_out                          false
% 3.54/0.98  
% 3.54/0.98  ------ Global Options
% 3.54/0.98  
% 3.54/0.98  --schedule                              default
% 3.54/0.98  --add_important_lit                     false
% 3.54/0.98  --prop_solver_per_cl                    1000
% 3.54/0.98  --min_unsat_core                        false
% 3.54/0.98  --soft_assumptions                      false
% 3.54/0.98  --soft_lemma_size                       3
% 3.54/0.98  --prop_impl_unit_size                   0
% 3.54/0.98  --prop_impl_unit                        []
% 3.54/0.98  --share_sel_clauses                     true
% 3.54/0.98  --reset_solvers                         false
% 3.54/0.98  --bc_imp_inh                            [conj_cone]
% 3.54/0.98  --conj_cone_tolerance                   3.
% 3.54/0.98  --extra_neg_conj                        none
% 3.54/0.98  --large_theory_mode                     true
% 3.54/0.98  --prolific_symb_bound                   200
% 3.54/0.98  --lt_threshold                          2000
% 3.54/0.98  --clause_weak_htbl                      true
% 3.54/0.98  --gc_record_bc_elim                     false
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing Options
% 3.54/0.98  
% 3.54/0.98  --preprocessing_flag                    true
% 3.54/0.98  --time_out_prep_mult                    0.1
% 3.54/0.98  --splitting_mode                        input
% 3.54/0.98  --splitting_grd                         true
% 3.54/0.98  --splitting_cvd                         false
% 3.54/0.98  --splitting_cvd_svl                     false
% 3.54/0.98  --splitting_nvd                         32
% 3.54/0.98  --sub_typing                            true
% 3.54/0.98  --prep_gs_sim                           true
% 3.54/0.98  --prep_unflatten                        true
% 3.54/0.98  --prep_res_sim                          true
% 3.54/0.98  --prep_upred                            true
% 3.54/0.98  --prep_sem_filter                       exhaustive
% 3.54/0.98  --prep_sem_filter_out                   false
% 3.54/0.98  --pred_elim                             true
% 3.54/0.98  --res_sim_input                         true
% 3.54/0.98  --eq_ax_congr_red                       true
% 3.54/0.98  --pure_diseq_elim                       true
% 3.54/0.98  --brand_transform                       false
% 3.54/0.98  --non_eq_to_eq                          false
% 3.54/0.98  --prep_def_merge                        true
% 3.54/0.98  --prep_def_merge_prop_impl              false
% 3.54/0.98  --prep_def_merge_mbd                    true
% 3.54/0.98  --prep_def_merge_tr_red                 false
% 3.54/0.98  --prep_def_merge_tr_cl                  false
% 3.54/0.98  --smt_preprocessing                     true
% 3.54/0.98  --smt_ac_axioms                         fast
% 3.54/0.98  --preprocessed_out                      false
% 3.54/0.98  --preprocessed_stats                    false
% 3.54/0.98  
% 3.54/0.98  ------ Abstraction refinement Options
% 3.54/0.98  
% 3.54/0.98  --abstr_ref                             []
% 3.54/0.98  --abstr_ref_prep                        false
% 3.54/0.98  --abstr_ref_until_sat                   false
% 3.54/0.98  --abstr_ref_sig_restrict                funpre
% 3.54/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.54/0.98  --abstr_ref_under                       []
% 3.54/0.98  
% 3.54/0.98  ------ SAT Options
% 3.54/0.98  
% 3.54/0.98  --sat_mode                              false
% 3.54/0.98  --sat_fm_restart_options                ""
% 3.54/0.98  --sat_gr_def                            false
% 3.54/0.98  --sat_epr_types                         true
% 3.54/0.98  --sat_non_cyclic_types                  false
% 3.54/0.98  --sat_finite_models                     false
% 3.54/0.98  --sat_fm_lemmas                         false
% 3.54/0.98  --sat_fm_prep                           false
% 3.54/0.98  --sat_fm_uc_incr                        true
% 3.54/0.98  --sat_out_model                         small
% 3.54/0.98  --sat_out_clauses                       false
% 3.54/0.98  
% 3.54/0.98  ------ QBF Options
% 3.54/0.98  
% 3.54/0.98  --qbf_mode                              false
% 3.54/0.98  --qbf_elim_univ                         false
% 3.54/0.98  --qbf_dom_inst                          none
% 3.54/0.98  --qbf_dom_pre_inst                      false
% 3.54/0.98  --qbf_sk_in                             false
% 3.54/0.98  --qbf_pred_elim                         true
% 3.54/0.98  --qbf_split                             512
% 3.54/0.98  
% 3.54/0.98  ------ BMC1 Options
% 3.54/0.98  
% 3.54/0.98  --bmc1_incremental                      false
% 3.54/0.98  --bmc1_axioms                           reachable_all
% 3.54/0.98  --bmc1_min_bound                        0
% 3.54/0.98  --bmc1_max_bound                        -1
% 3.54/0.98  --bmc1_max_bound_default                -1
% 3.54/0.98  --bmc1_symbol_reachability              true
% 3.54/0.98  --bmc1_property_lemmas                  false
% 3.54/0.98  --bmc1_k_induction                      false
% 3.54/0.98  --bmc1_non_equiv_states                 false
% 3.54/0.98  --bmc1_deadlock                         false
% 3.54/0.98  --bmc1_ucm                              false
% 3.54/0.98  --bmc1_add_unsat_core                   none
% 3.54/0.98  --bmc1_unsat_core_children              false
% 3.54/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.54/0.98  --bmc1_out_stat                         full
% 3.54/0.98  --bmc1_ground_init                      false
% 3.54/0.98  --bmc1_pre_inst_next_state              false
% 3.54/0.98  --bmc1_pre_inst_state                   false
% 3.54/0.98  --bmc1_pre_inst_reach_state             false
% 3.54/0.98  --bmc1_out_unsat_core                   false
% 3.54/0.98  --bmc1_aig_witness_out                  false
% 3.54/0.98  --bmc1_verbose                          false
% 3.54/0.98  --bmc1_dump_clauses_tptp                false
% 3.54/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.54/0.98  --bmc1_dump_file                        -
% 3.54/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.54/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.54/0.98  --bmc1_ucm_extend_mode                  1
% 3.54/0.98  --bmc1_ucm_init_mode                    2
% 3.54/0.98  --bmc1_ucm_cone_mode                    none
% 3.54/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.54/0.98  --bmc1_ucm_relax_model                  4
% 3.54/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.54/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.54/0.98  --bmc1_ucm_layered_model                none
% 3.54/0.98  --bmc1_ucm_max_lemma_size               10
% 3.54/0.98  
% 3.54/0.98  ------ AIG Options
% 3.54/0.98  
% 3.54/0.98  --aig_mode                              false
% 3.54/0.98  
% 3.54/0.98  ------ Instantiation Options
% 3.54/0.98  
% 3.54/0.98  --instantiation_flag                    true
% 3.54/0.98  --inst_sos_flag                         false
% 3.54/0.98  --inst_sos_phase                        true
% 3.54/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.54/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.54/0.98  --inst_lit_sel_side                     num_symb
% 3.54/0.98  --inst_solver_per_active                1400
% 3.54/0.98  --inst_solver_calls_frac                1.
% 3.54/0.98  --inst_passive_queue_type               priority_queues
% 3.54/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.54/0.98  --inst_passive_queues_freq              [25;2]
% 3.54/0.98  --inst_dismatching                      true
% 3.54/0.98  --inst_eager_unprocessed_to_passive     true
% 3.54/0.98  --inst_prop_sim_given                   true
% 3.54/0.98  --inst_prop_sim_new                     false
% 3.54/0.98  --inst_subs_new                         false
% 3.54/0.98  --inst_eq_res_simp                      false
% 3.54/0.98  --inst_subs_given                       false
% 3.54/0.98  --inst_orphan_elimination               true
% 3.54/0.98  --inst_learning_loop_flag               true
% 3.54/0.98  --inst_learning_start                   3000
% 3.54/0.98  --inst_learning_factor                  2
% 3.54/0.98  --inst_start_prop_sim_after_learn       3
% 3.54/0.98  --inst_sel_renew                        solver
% 3.54/0.98  --inst_lit_activity_flag                true
% 3.54/0.98  --inst_restr_to_given                   false
% 3.54/0.98  --inst_activity_threshold               500
% 3.54/0.98  --inst_out_proof                        true
% 3.54/0.98  
% 3.54/0.98  ------ Resolution Options
% 3.54/0.98  
% 3.54/0.98  --resolution_flag                       true
% 3.54/0.98  --res_lit_sel                           adaptive
% 3.54/0.98  --res_lit_sel_side                      none
% 3.54/0.98  --res_ordering                          kbo
% 3.54/0.98  --res_to_prop_solver                    active
% 3.54/0.98  --res_prop_simpl_new                    false
% 3.54/0.98  --res_prop_simpl_given                  true
% 3.54/0.98  --res_passive_queue_type                priority_queues
% 3.54/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.54/0.98  --res_passive_queues_freq               [15;5]
% 3.54/0.98  --res_forward_subs                      full
% 3.54/0.98  --res_backward_subs                     full
% 3.54/0.98  --res_forward_subs_resolution           true
% 3.54/0.98  --res_backward_subs_resolution          true
% 3.54/0.98  --res_orphan_elimination                true
% 3.54/0.98  --res_time_limit                        2.
% 3.54/0.98  --res_out_proof                         true
% 3.54/0.98  
% 3.54/0.98  ------ Superposition Options
% 3.54/0.98  
% 3.54/0.98  --superposition_flag                    true
% 3.54/0.98  --sup_passive_queue_type                priority_queues
% 3.54/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.54/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.54/0.98  --demod_completeness_check              fast
% 3.54/0.98  --demod_use_ground                      true
% 3.54/0.98  --sup_to_prop_solver                    passive
% 3.54/0.98  --sup_prop_simpl_new                    true
% 3.54/0.98  --sup_prop_simpl_given                  true
% 3.54/0.98  --sup_fun_splitting                     false
% 3.54/0.98  --sup_smt_interval                      50000
% 3.54/0.98  
% 3.54/0.98  ------ Superposition Simplification Setup
% 3.54/0.98  
% 3.54/0.98  --sup_indices_passive                   []
% 3.54/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.54/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.98  --sup_full_bw                           [BwDemod]
% 3.54/0.98  --sup_immed_triv                        [TrivRules]
% 3.54/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.98  --sup_immed_bw_main                     []
% 3.54/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.54/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/0.98  
% 3.54/0.98  ------ Combination Options
% 3.54/0.98  
% 3.54/0.98  --comb_res_mult                         3
% 3.54/0.98  --comb_sup_mult                         2
% 3.54/0.98  --comb_inst_mult                        10
% 3.54/0.98  
% 3.54/0.98  ------ Debug Options
% 3.54/0.98  
% 3.54/0.98  --dbg_backtrace                         false
% 3.54/0.98  --dbg_dump_prop_clauses                 false
% 3.54/0.98  --dbg_dump_prop_clauses_file            -
% 3.54/0.98  --dbg_out_stat                          false
% 3.54/0.98  ------ Parsing...
% 3.54/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/0.98  ------ Proving...
% 3.54/0.98  ------ Problem Properties 
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  clauses                                 53
% 3.54/0.98  conjectures                             17
% 3.54/0.98  EPR                                     19
% 3.54/0.98  Horn                                    42
% 3.54/0.98  unary                                   18
% 3.54/0.98  binary                                  9
% 3.54/0.98  lits                                    178
% 3.54/0.98  lits eq                                 18
% 3.54/0.98  fd_pure                                 0
% 3.54/0.98  fd_pseudo                               0
% 3.54/0.98  fd_cond                                 0
% 3.54/0.98  fd_pseudo_cond                          3
% 3.54/0.98  AC symbols                              0
% 3.54/0.98  
% 3.54/0.98  ------ Schedule dynamic 5 is on 
% 3.54/0.98  
% 3.54/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ 
% 3.54/0.98  Current options:
% 3.54/0.98  ------ 
% 3.54/0.98  
% 3.54/0.98  ------ Input Options
% 3.54/0.98  
% 3.54/0.98  --out_options                           all
% 3.54/0.98  --tptp_safe_out                         true
% 3.54/0.98  --problem_path                          ""
% 3.54/0.98  --include_path                          ""
% 3.54/0.98  --clausifier                            res/vclausify_rel
% 3.54/0.98  --clausifier_options                    --mode clausify
% 3.54/0.98  --stdin                                 false
% 3.54/0.98  --stats_out                             all
% 3.54/0.98  
% 3.54/0.98  ------ General Options
% 3.54/0.98  
% 3.54/0.98  --fof                                   false
% 3.54/0.98  --time_out_real                         305.
% 3.54/0.98  --time_out_virtual                      -1.
% 3.54/0.98  --symbol_type_check                     false
% 3.54/0.98  --clausify_out                          false
% 3.54/0.98  --sig_cnt_out                           false
% 3.54/0.98  --trig_cnt_out                          false
% 3.54/0.98  --trig_cnt_out_tolerance                1.
% 3.54/0.98  --trig_cnt_out_sk_spl                   false
% 3.54/0.98  --abstr_cl_out                          false
% 3.54/0.98  
% 3.54/0.98  ------ Global Options
% 3.54/0.98  
% 3.54/0.98  --schedule                              default
% 3.54/0.98  --add_important_lit                     false
% 3.54/0.98  --prop_solver_per_cl                    1000
% 3.54/0.98  --min_unsat_core                        false
% 3.54/0.98  --soft_assumptions                      false
% 3.54/0.98  --soft_lemma_size                       3
% 3.54/0.98  --prop_impl_unit_size                   0
% 3.54/0.98  --prop_impl_unit                        []
% 3.54/0.98  --share_sel_clauses                     true
% 3.54/0.98  --reset_solvers                         false
% 3.54/0.98  --bc_imp_inh                            [conj_cone]
% 3.54/0.98  --conj_cone_tolerance                   3.
% 3.54/0.98  --extra_neg_conj                        none
% 3.54/0.98  --large_theory_mode                     true
% 3.54/0.98  --prolific_symb_bound                   200
% 3.54/0.98  --lt_threshold                          2000
% 3.54/0.98  --clause_weak_htbl                      true
% 3.54/0.98  --gc_record_bc_elim                     false
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing Options
% 3.54/0.98  
% 3.54/0.98  --preprocessing_flag                    true
% 3.54/0.98  --time_out_prep_mult                    0.1
% 3.54/0.98  --splitting_mode                        input
% 3.54/0.98  --splitting_grd                         true
% 3.54/0.98  --splitting_cvd                         false
% 3.54/0.98  --splitting_cvd_svl                     false
% 3.54/0.98  --splitting_nvd                         32
% 3.54/0.98  --sub_typing                            true
% 3.54/0.98  --prep_gs_sim                           true
% 3.54/0.98  --prep_unflatten                        true
% 3.54/0.98  --prep_res_sim                          true
% 3.54/0.98  --prep_upred                            true
% 3.54/0.98  --prep_sem_filter                       exhaustive
% 3.54/0.98  --prep_sem_filter_out                   false
% 3.54/0.98  --pred_elim                             true
% 3.54/0.98  --res_sim_input                         true
% 3.54/0.98  --eq_ax_congr_red                       true
% 3.54/0.98  --pure_diseq_elim                       true
% 3.54/0.98  --brand_transform                       false
% 3.54/0.98  --non_eq_to_eq                          false
% 3.54/0.98  --prep_def_merge                        true
% 3.54/0.98  --prep_def_merge_prop_impl              false
% 3.54/0.98  --prep_def_merge_mbd                    true
% 3.54/0.98  --prep_def_merge_tr_red                 false
% 3.54/0.98  --prep_def_merge_tr_cl                  false
% 3.54/0.98  --smt_preprocessing                     true
% 3.54/0.98  --smt_ac_axioms                         fast
% 3.54/0.98  --preprocessed_out                      false
% 3.54/0.98  --preprocessed_stats                    false
% 3.54/0.98  
% 3.54/0.98  ------ Abstraction refinement Options
% 3.54/0.98  
% 3.54/0.98  --abstr_ref                             []
% 3.54/0.98  --abstr_ref_prep                        false
% 3.54/0.98  --abstr_ref_until_sat                   false
% 3.54/0.98  --abstr_ref_sig_restrict                funpre
% 3.54/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.54/0.98  --abstr_ref_under                       []
% 3.54/0.98  
% 3.54/0.98  ------ SAT Options
% 3.54/0.98  
% 3.54/0.98  --sat_mode                              false
% 3.54/0.98  --sat_fm_restart_options                ""
% 3.54/0.98  --sat_gr_def                            false
% 3.54/0.98  --sat_epr_types                         true
% 3.54/0.98  --sat_non_cyclic_types                  false
% 3.54/0.98  --sat_finite_models                     false
% 3.54/0.98  --sat_fm_lemmas                         false
% 3.54/0.98  --sat_fm_prep                           false
% 3.54/0.98  --sat_fm_uc_incr                        true
% 3.54/0.98  --sat_out_model                         small
% 3.54/0.98  --sat_out_clauses                       false
% 3.54/0.98  
% 3.54/0.98  ------ QBF Options
% 3.54/0.98  
% 3.54/0.98  --qbf_mode                              false
% 3.54/0.98  --qbf_elim_univ                         false
% 3.54/0.98  --qbf_dom_inst                          none
% 3.54/0.98  --qbf_dom_pre_inst                      false
% 3.54/0.98  --qbf_sk_in                             false
% 3.54/0.98  --qbf_pred_elim                         true
% 3.54/0.98  --qbf_split                             512
% 3.54/0.98  
% 3.54/0.98  ------ BMC1 Options
% 3.54/0.98  
% 3.54/0.98  --bmc1_incremental                      false
% 3.54/0.98  --bmc1_axioms                           reachable_all
% 3.54/0.98  --bmc1_min_bound                        0
% 3.54/0.98  --bmc1_max_bound                        -1
% 3.54/0.98  --bmc1_max_bound_default                -1
% 3.54/0.98  --bmc1_symbol_reachability              true
% 3.54/0.98  --bmc1_property_lemmas                  false
% 3.54/0.98  --bmc1_k_induction                      false
% 3.54/0.98  --bmc1_non_equiv_states                 false
% 3.54/0.98  --bmc1_deadlock                         false
% 3.54/0.98  --bmc1_ucm                              false
% 3.54/0.98  --bmc1_add_unsat_core                   none
% 3.54/0.98  --bmc1_unsat_core_children              false
% 3.54/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.54/0.98  --bmc1_out_stat                         full
% 3.54/0.98  --bmc1_ground_init                      false
% 3.54/0.98  --bmc1_pre_inst_next_state              false
% 3.54/0.98  --bmc1_pre_inst_state                   false
% 3.54/0.98  --bmc1_pre_inst_reach_state             false
% 3.54/0.98  --bmc1_out_unsat_core                   false
% 3.54/0.98  --bmc1_aig_witness_out                  false
% 3.54/0.98  --bmc1_verbose                          false
% 3.54/0.98  --bmc1_dump_clauses_tptp                false
% 3.54/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.54/0.98  --bmc1_dump_file                        -
% 3.54/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.54/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.54/0.98  --bmc1_ucm_extend_mode                  1
% 3.54/0.98  --bmc1_ucm_init_mode                    2
% 3.54/0.98  --bmc1_ucm_cone_mode                    none
% 3.54/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.54/0.98  --bmc1_ucm_relax_model                  4
% 3.54/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.54/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.54/0.98  --bmc1_ucm_layered_model                none
% 3.54/0.98  --bmc1_ucm_max_lemma_size               10
% 3.54/0.98  
% 3.54/0.98  ------ AIG Options
% 3.54/0.98  
% 3.54/0.98  --aig_mode                              false
% 3.54/0.98  
% 3.54/0.98  ------ Instantiation Options
% 3.54/0.98  
% 3.54/0.98  --instantiation_flag                    true
% 3.54/0.98  --inst_sos_flag                         false
% 3.54/0.98  --inst_sos_phase                        true
% 3.54/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.54/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.54/0.98  --inst_lit_sel_side                     none
% 3.54/0.98  --inst_solver_per_active                1400
% 3.54/0.98  --inst_solver_calls_frac                1.
% 3.54/0.98  --inst_passive_queue_type               priority_queues
% 3.54/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.54/0.98  --inst_passive_queues_freq              [25;2]
% 3.54/0.98  --inst_dismatching                      true
% 3.54/0.98  --inst_eager_unprocessed_to_passive     true
% 3.54/0.98  --inst_prop_sim_given                   true
% 3.54/0.98  --inst_prop_sim_new                     false
% 3.54/0.98  --inst_subs_new                         false
% 3.54/0.98  --inst_eq_res_simp                      false
% 3.54/0.98  --inst_subs_given                       false
% 3.54/0.98  --inst_orphan_elimination               true
% 3.54/0.98  --inst_learning_loop_flag               true
% 3.54/0.98  --inst_learning_start                   3000
% 3.54/0.98  --inst_learning_factor                  2
% 3.54/0.98  --inst_start_prop_sim_after_learn       3
% 3.54/0.98  --inst_sel_renew                        solver
% 3.54/0.98  --inst_lit_activity_flag                true
% 3.54/0.98  --inst_restr_to_given                   false
% 3.54/0.98  --inst_activity_threshold               500
% 3.54/0.98  --inst_out_proof                        true
% 3.54/0.98  
% 3.54/0.98  ------ Resolution Options
% 3.54/0.98  
% 3.54/0.98  --resolution_flag                       false
% 3.54/0.98  --res_lit_sel                           adaptive
% 3.54/0.98  --res_lit_sel_side                      none
% 3.54/0.98  --res_ordering                          kbo
% 3.54/0.98  --res_to_prop_solver                    active
% 3.54/0.98  --res_prop_simpl_new                    false
% 3.54/0.98  --res_prop_simpl_given                  true
% 3.54/0.98  --res_passive_queue_type                priority_queues
% 3.54/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.54/0.98  --res_passive_queues_freq               [15;5]
% 3.54/0.98  --res_forward_subs                      full
% 3.54/0.98  --res_backward_subs                     full
% 3.54/0.98  --res_forward_subs_resolution           true
% 3.54/0.98  --res_backward_subs_resolution          true
% 3.54/0.98  --res_orphan_elimination                true
% 3.54/0.98  --res_time_limit                        2.
% 3.54/0.98  --res_out_proof                         true
% 3.54/0.98  
% 3.54/0.98  ------ Superposition Options
% 3.54/0.98  
% 3.54/0.98  --superposition_flag                    true
% 3.54/0.98  --sup_passive_queue_type                priority_queues
% 3.54/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.54/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.54/0.98  --demod_completeness_check              fast
% 3.54/0.98  --demod_use_ground                      true
% 3.54/0.98  --sup_to_prop_solver                    passive
% 3.54/0.98  --sup_prop_simpl_new                    true
% 3.54/0.98  --sup_prop_simpl_given                  true
% 3.54/0.98  --sup_fun_splitting                     false
% 3.54/0.98  --sup_smt_interval                      50000
% 3.54/0.98  
% 3.54/0.98  ------ Superposition Simplification Setup
% 3.54/0.98  
% 3.54/0.98  --sup_indices_passive                   []
% 3.54/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.54/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.98  --sup_full_bw                           [BwDemod]
% 3.54/0.98  --sup_immed_triv                        [TrivRules]
% 3.54/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.98  --sup_immed_bw_main                     []
% 3.54/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.54/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/0.98  
% 3.54/0.98  ------ Combination Options
% 3.54/0.98  
% 3.54/0.98  --comb_res_mult                         3
% 3.54/0.98  --comb_sup_mult                         2
% 3.54/0.98  --comb_inst_mult                        10
% 3.54/0.98  
% 3.54/0.98  ------ Debug Options
% 3.54/0.98  
% 3.54/0.98  --dbg_backtrace                         false
% 3.54/0.98  --dbg_dump_prop_clauses                 false
% 3.54/0.98  --dbg_dump_prop_clauses_file            -
% 3.54/0.98  --dbg_out_stat                          false
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ Proving...
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  % SZS status Theorem for theBenchmark.p
% 3.54/0.98  
% 3.54/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.54/0.98  
% 3.54/0.98  fof(f5,axiom,(
% 3.54/0.98    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f24,plain,(
% 3.54/0.98    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.54/0.98    inference(rectify,[],[f5])).
% 3.54/0.98  
% 3.54/0.98  fof(f29,plain,(
% 3.54/0.98    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.54/0.98    inference(ennf_transformation,[],[f24])).
% 3.54/0.98  
% 3.54/0.98  fof(f30,plain,(
% 3.54/0.98    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.54/0.98    inference(flattening,[],[f29])).
% 3.54/0.98  
% 3.54/0.98  fof(f56,plain,(
% 3.54/0.98    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.54/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.54/0.98  
% 3.54/0.98  fof(f57,plain,(
% 3.54/0.98    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.54/0.98    inference(definition_folding,[],[f30,f56])).
% 3.54/0.98  
% 3.54/0.98  fof(f66,plain,(
% 3.54/0.98    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.54/0.98    inference(nnf_transformation,[],[f57])).
% 3.54/0.98  
% 3.54/0.98  fof(f67,plain,(
% 3.54/0.98    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.54/0.98    inference(flattening,[],[f66])).
% 3.54/0.98  
% 3.54/0.98  fof(f68,plain,(
% 3.54/0.98    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.54/0.98    inference(rectify,[],[f67])).
% 3.54/0.98  
% 3.54/0.98  fof(f69,plain,(
% 3.54/0.98    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.54/0.98    introduced(choice_axiom,[])).
% 3.54/0.98  
% 3.54/0.98  fof(f70,plain,(
% 3.54/0.98    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.54/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f68,f69])).
% 3.54/0.98  
% 3.54/0.98  fof(f98,plain,(
% 3.54/0.98    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f70])).
% 3.54/0.98  
% 3.54/0.98  fof(f22,conjecture,(
% 3.54/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f23,negated_conjecture,(
% 3.54/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.54/0.98    inference(negated_conjecture,[],[f22])).
% 3.54/0.98  
% 3.54/0.98  fof(f54,plain,(
% 3.54/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.54/0.98    inference(ennf_transformation,[],[f23])).
% 3.54/0.98  
% 3.54/0.98  fof(f55,plain,(
% 3.54/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.54/0.98    inference(flattening,[],[f54])).
% 3.54/0.98  
% 3.54/0.98  fof(f83,plain,(
% 3.54/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK10) & sK10 = X5 & m1_subset_1(sK10,u1_struct_0(X2)))) )),
% 3.54/0.98    introduced(choice_axiom,[])).
% 3.54/0.98  
% 3.54/0.98  fof(f82,plain,(
% 3.54/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK9) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK9 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK9,u1_struct_0(X3)))) )),
% 3.54/0.98    introduced(choice_axiom,[])).
% 3.54/0.98  
% 3.54/0.98  fof(f81,plain,(
% 3.54/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK8,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK8),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK8,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK8))) )),
% 3.54/0.98    introduced(choice_axiom,[])).
% 3.54/0.98  
% 3.54/0.98  fof(f80,plain,(
% 3.54/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK7,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK7,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK7))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK7 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK7,X0) & ~v2_struct_0(sK7))) )),
% 3.54/0.98    introduced(choice_axiom,[])).
% 3.54/0.98  
% 3.54/0.98  fof(f79,plain,(
% 3.54/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK6,X1,k3_tmap_1(X0,X1,X3,sK6,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK6))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 3.54/0.98    introduced(choice_axiom,[])).
% 3.54/0.98  
% 3.54/0.98  fof(f78,plain,(
% 3.54/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK5,X4,X5) & r1_tmap_1(X2,sK5,k3_tmap_1(X0,sK5,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))) )),
% 3.54/0.98    introduced(choice_axiom,[])).
% 3.54/0.98  
% 3.54/0.98  fof(f77,plain,(
% 3.54/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK4,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 3.54/0.98    introduced(choice_axiom,[])).
% 3.54/0.98  
% 3.54/0.98  fof(f84,plain,(
% 3.54/0.98    ((((((~r1_tmap_1(sK7,sK5,sK8,sK9) & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) & sK9 = sK10 & m1_subset_1(sK10,u1_struct_0(sK6))) & m1_subset_1(sK9,u1_struct_0(sK7))) & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(sK8)) & m1_pre_topc(sK7,sK4) & ~v2_struct_0(sK7)) & m1_pre_topc(sK6,sK4) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 3.54/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f55,f83,f82,f81,f80,f79,f78,f77])).
% 3.54/0.98  
% 3.54/0.98  fof(f135,plain,(
% 3.54/0.98    m1_pre_topc(sK6,sK4)),
% 3.54/0.98    inference(cnf_transformation,[],[f84])).
% 3.54/0.98  
% 3.54/0.98  fof(f15,axiom,(
% 3.54/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f43,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.54/0.98    inference(ennf_transformation,[],[f15])).
% 3.54/0.98  
% 3.54/0.98  fof(f116,plain,(
% 3.54/0.98    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f43])).
% 3.54/0.98  
% 3.54/0.98  fof(f141,plain,(
% 3.54/0.98    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7),
% 3.54/0.98    inference(cnf_transformation,[],[f84])).
% 3.54/0.98  
% 3.54/0.98  fof(f130,plain,(
% 3.54/0.98    l1_pre_topc(sK4)),
% 3.54/0.98    inference(cnf_transformation,[],[f84])).
% 3.54/0.98  
% 3.54/0.98  fof(f137,plain,(
% 3.54/0.98    m1_pre_topc(sK7,sK4)),
% 3.54/0.98    inference(cnf_transformation,[],[f84])).
% 3.54/0.98  
% 3.54/0.98  fof(f7,axiom,(
% 3.54/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f32,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.54/0.98    inference(ennf_transformation,[],[f7])).
% 3.54/0.98  
% 3.54/0.98  fof(f106,plain,(
% 3.54/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f32])).
% 3.54/0.98  
% 3.54/0.98  fof(f18,axiom,(
% 3.54/0.98    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f47,plain,(
% 3.54/0.98    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.54/0.98    inference(ennf_transformation,[],[f18])).
% 3.54/0.98  
% 3.54/0.98  fof(f122,plain,(
% 3.54/0.98    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f47])).
% 3.54/0.98  
% 3.54/0.98  fof(f12,axiom,(
% 3.54/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f38,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.54/0.98    inference(ennf_transformation,[],[f12])).
% 3.54/0.98  
% 3.54/0.98  fof(f72,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.54/0.98    inference(nnf_transformation,[],[f38])).
% 3.54/0.98  
% 3.54/0.98  fof(f112,plain,(
% 3.54/0.98    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f72])).
% 3.54/0.98  
% 3.54/0.98  fof(f3,axiom,(
% 3.54/0.98    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f25,plain,(
% 3.54/0.98    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.54/0.98    inference(ennf_transformation,[],[f3])).
% 3.54/0.98  
% 3.54/0.98  fof(f26,plain,(
% 3.54/0.98    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 3.54/0.98    inference(flattening,[],[f25])).
% 3.54/0.98  
% 3.54/0.98  fof(f90,plain,(
% 3.54/0.98    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f26])).
% 3.54/0.98  
% 3.54/0.98  fof(f9,axiom,(
% 3.54/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f34,plain,(
% 3.54/0.98    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.54/0.98    inference(ennf_transformation,[],[f9])).
% 3.54/0.98  
% 3.54/0.98  fof(f108,plain,(
% 3.54/0.98    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.54/0.98    inference(cnf_transformation,[],[f34])).
% 3.54/0.98  
% 3.54/0.98  fof(f8,axiom,(
% 3.54/0.98    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f33,plain,(
% 3.54/0.98    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.54/0.98    inference(ennf_transformation,[],[f8])).
% 3.54/0.98  
% 3.54/0.98  fof(f107,plain,(
% 3.54/0.98    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f33])).
% 3.54/0.98  
% 3.54/0.98  fof(f14,axiom,(
% 3.54/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f41,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.54/0.98    inference(ennf_transformation,[],[f14])).
% 3.54/0.98  
% 3.54/0.98  fof(f42,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.54/0.98    inference(flattening,[],[f41])).
% 3.54/0.98  
% 3.54/0.98  fof(f115,plain,(
% 3.54/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f42])).
% 3.54/0.98  
% 3.54/0.98  fof(f139,plain,(
% 3.54/0.98    v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))),
% 3.54/0.98    inference(cnf_transformation,[],[f84])).
% 3.54/0.98  
% 3.54/0.98  fof(f138,plain,(
% 3.54/0.98    v1_funct_1(sK8)),
% 3.54/0.98    inference(cnf_transformation,[],[f84])).
% 3.54/0.98  
% 3.54/0.98  fof(f21,axiom,(
% 3.54/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f52,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.54/0.98    inference(ennf_transformation,[],[f21])).
% 3.54/0.98  
% 3.54/0.98  fof(f53,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.54/0.98    inference(flattening,[],[f52])).
% 3.54/0.98  
% 3.54/0.98  fof(f127,plain,(
% 3.54/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f53])).
% 3.54/0.98  
% 3.54/0.98  fof(f131,plain,(
% 3.54/0.98    ~v2_struct_0(sK5)),
% 3.54/0.98    inference(cnf_transformation,[],[f84])).
% 3.54/0.98  
% 3.54/0.98  fof(f132,plain,(
% 3.54/0.98    v2_pre_topc(sK5)),
% 3.54/0.98    inference(cnf_transformation,[],[f84])).
% 3.54/0.98  
% 3.54/0.98  fof(f133,plain,(
% 3.54/0.98    l1_pre_topc(sK5)),
% 3.54/0.98    inference(cnf_transformation,[],[f84])).
% 3.54/0.98  
% 3.54/0.98  fof(f140,plain,(
% 3.54/0.98    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))),
% 3.54/0.98    inference(cnf_transformation,[],[f84])).
% 3.54/0.98  
% 3.54/0.98  fof(f128,plain,(
% 3.54/0.98    ~v2_struct_0(sK4)),
% 3.54/0.98    inference(cnf_transformation,[],[f84])).
% 3.54/0.98  
% 3.54/0.98  fof(f129,plain,(
% 3.54/0.98    v2_pre_topc(sK4)),
% 3.54/0.98    inference(cnf_transformation,[],[f84])).
% 3.54/0.98  
% 3.54/0.98  fof(f13,axiom,(
% 3.54/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f39,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.54/0.98    inference(ennf_transformation,[],[f13])).
% 3.54/0.98  
% 3.54/0.98  fof(f40,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.54/0.98    inference(flattening,[],[f39])).
% 3.54/0.98  
% 3.54/0.98  fof(f114,plain,(
% 3.54/0.98    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f40])).
% 3.54/0.98  
% 3.54/0.98  fof(f136,plain,(
% 3.54/0.98    ~v2_struct_0(sK7)),
% 3.54/0.98    inference(cnf_transformation,[],[f84])).
% 3.54/0.98  
% 3.54/0.98  fof(f4,axiom,(
% 3.54/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f27,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.54/0.98    inference(ennf_transformation,[],[f4])).
% 3.54/0.98  
% 3.54/0.98  fof(f28,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.54/0.98    inference(flattening,[],[f27])).
% 3.54/0.98  
% 3.54/0.98  fof(f91,plain,(
% 3.54/0.98    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f28])).
% 3.54/0.98  
% 3.54/0.98  fof(f145,plain,(
% 3.54/0.98    r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)),
% 3.54/0.98    inference(cnf_transformation,[],[f84])).
% 3.54/0.98  
% 3.54/0.98  fof(f144,plain,(
% 3.54/0.98    sK9 = sK10),
% 3.54/0.98    inference(cnf_transformation,[],[f84])).
% 3.54/0.98  
% 3.54/0.98  fof(f6,axiom,(
% 3.54/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f31,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.54/0.98    inference(ennf_transformation,[],[f6])).
% 3.54/0.98  
% 3.54/0.98  fof(f71,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.54/0.98    inference(nnf_transformation,[],[f31])).
% 3.54/0.98  
% 3.54/0.98  fof(f105,plain,(
% 3.54/0.98    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f71])).
% 3.54/0.98  
% 3.54/0.98  fof(f16,axiom,(
% 3.54/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f44,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.54/0.98    inference(ennf_transformation,[],[f16])).
% 3.54/0.98  
% 3.54/0.98  fof(f45,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.54/0.98    inference(flattening,[],[f44])).
% 3.54/0.98  
% 3.54/0.98  fof(f73,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.54/0.98    inference(nnf_transformation,[],[f45])).
% 3.54/0.98  
% 3.54/0.98  fof(f74,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.54/0.98    inference(flattening,[],[f73])).
% 3.54/0.98  
% 3.54/0.98  fof(f119,plain,(
% 3.54/0.98    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f74])).
% 3.54/0.98  
% 3.54/0.98  fof(f150,plain,(
% 3.54/0.98    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.54/0.98    inference(equality_resolution,[],[f119])).
% 3.54/0.98  
% 3.54/0.98  fof(f17,axiom,(
% 3.54/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f46,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.54/0.98    inference(ennf_transformation,[],[f17])).
% 3.54/0.98  
% 3.54/0.98  fof(f121,plain,(
% 3.54/0.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f46])).
% 3.54/0.98  
% 3.54/0.98  fof(f20,axiom,(
% 3.54/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f50,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.54/0.98    inference(ennf_transformation,[],[f20])).
% 3.54/0.98  
% 3.54/0.98  fof(f51,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.54/0.98    inference(flattening,[],[f50])).
% 3.54/0.98  
% 3.54/0.98  fof(f76,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4))) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.54/0.98    inference(nnf_transformation,[],[f51])).
% 3.54/0.98  
% 3.54/0.98  fof(f126,plain,(
% 3.54/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f76])).
% 3.54/0.98  
% 3.54/0.98  fof(f152,plain,(
% 3.54/0.98    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/0.98    inference(equality_resolution,[],[f126])).
% 3.54/0.98  
% 3.54/0.98  fof(f10,axiom,(
% 3.54/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f35,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.54/0.98    inference(ennf_transformation,[],[f10])).
% 3.54/0.98  
% 3.54/0.98  fof(f36,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.54/0.98    inference(flattening,[],[f35])).
% 3.54/0.98  
% 3.54/0.98  fof(f110,plain,(
% 3.54/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f36])).
% 3.54/0.98  
% 3.54/0.98  fof(f134,plain,(
% 3.54/0.98    ~v2_struct_0(sK6)),
% 3.54/0.98    inference(cnf_transformation,[],[f84])).
% 3.54/0.98  
% 3.54/0.98  fof(f146,plain,(
% 3.54/0.98    ~r1_tmap_1(sK7,sK5,sK8,sK9)),
% 3.54/0.98    inference(cnf_transformation,[],[f84])).
% 3.54/0.98  
% 3.54/0.98  fof(f143,plain,(
% 3.54/0.98    m1_subset_1(sK10,u1_struct_0(sK6))),
% 3.54/0.98    inference(cnf_transformation,[],[f84])).
% 3.54/0.98  
% 3.54/0.98  cnf(c_18,plain,
% 3.54/0.98      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 3.54/0.98      | ~ v2_pre_topc(X0)
% 3.54/0.98      | ~ l1_pre_topc(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_9570,plain,
% 3.54/0.98      ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
% 3.54/0.98      | ~ v2_pre_topc(sK7)
% 3.54/0.98      | ~ l1_pre_topc(sK7) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_54,negated_conjecture,
% 3.54/0.98      ( m1_pre_topc(sK6,sK4) ),
% 3.54/0.98      inference(cnf_transformation,[],[f135]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3884,plain,
% 3.54/0.98      ( m1_pre_topc(sK6,sK4) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_32,plain,
% 3.54/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.54/0.98      | ~ l1_pre_topc(X1)
% 3.54/0.98      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.54/0.98      inference(cnf_transformation,[],[f116]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3897,plain,
% 3.54/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.54/0.98      | l1_pre_topc(X1) != iProver_top
% 3.54/0.98      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8337,plain,
% 3.54/0.98      ( l1_pre_topc(sK4) != iProver_top
% 3.54/0.98      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_3884,c_3897]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_48,negated_conjecture,
% 3.54/0.98      ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
% 3.54/0.98      inference(cnf_transformation,[],[f141]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8348,plain,
% 3.54/0.98      ( l1_pre_topc(sK4) != iProver_top
% 3.54/0.98      | v1_pre_topc(sK7) = iProver_top ),
% 3.54/0.98      inference(light_normalisation,[status(thm)],[c_8337,c_48]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_59,negated_conjecture,
% 3.54/0.98      ( l1_pre_topc(sK4) ),
% 3.54/0.98      inference(cnf_transformation,[],[f130]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_64,plain,
% 3.54/0.98      ( l1_pre_topc(sK4) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_52,negated_conjecture,
% 3.54/0.98      ( m1_pre_topc(sK7,sK4) ),
% 3.54/0.98      inference(cnf_transformation,[],[f137]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3886,plain,
% 3.54/0.98      ( m1_pre_topc(sK7,sK4) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_21,plain,
% 3.54/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f106]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3904,plain,
% 3.54/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.54/0.98      | l1_pre_topc(X1) != iProver_top
% 3.54/0.98      | l1_pre_topc(X0) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6892,plain,
% 3.54/0.98      ( l1_pre_topc(sK4) != iProver_top
% 3.54/0.98      | l1_pre_topc(sK7) = iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_3886,c_3904]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6893,plain,
% 3.54/0.98      ( l1_pre_topc(sK4) != iProver_top
% 3.54/0.98      | l1_pre_topc(sK6) = iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_3884,c_3904]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_37,plain,
% 3.54/0.98      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f122]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3895,plain,
% 3.54/0.98      ( m1_pre_topc(X0,X0) = iProver_top
% 3.54/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_28,plain,
% 3.54/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.54/0.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.54/0.98      | ~ l1_pre_topc(X0)
% 3.54/0.98      | ~ l1_pre_topc(X1) ),
% 3.54/0.98      inference(cnf_transformation,[],[f112]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_345,plain,
% 3.54/0.98      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.54/0.98      | ~ m1_pre_topc(X0,X1)
% 3.54/0.98      | ~ l1_pre_topc(X1) ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_28,c_21]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_346,plain,
% 3.54/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.54/0.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.54/0.98      | ~ l1_pre_topc(X1) ),
% 3.54/0.98      inference(renaming,[status(thm)],[c_345]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3876,plain,
% 3.54/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.54/0.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.54/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_5938,plain,
% 3.54/0.98      ( m1_pre_topc(X0,sK6) != iProver_top
% 3.54/0.98      | m1_pre_topc(X0,sK7) = iProver_top
% 3.54/0.98      | l1_pre_topc(sK6) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_48,c_3876]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6313,plain,
% 3.54/0.98      ( m1_pre_topc(sK6,sK7) = iProver_top
% 3.54/0.98      | l1_pre_topc(sK6) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_3895,c_5938]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8338,plain,
% 3.54/0.98      ( l1_pre_topc(sK6) != iProver_top
% 3.54/0.98      | l1_pre_topc(sK7) != iProver_top
% 3.54/0.98      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_6313,c_3897]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8342,plain,
% 3.54/0.98      ( l1_pre_topc(sK6) != iProver_top
% 3.54/0.98      | l1_pre_topc(sK7) != iProver_top
% 3.54/0.98      | v1_pre_topc(sK7) = iProver_top ),
% 3.54/0.98      inference(light_normalisation,[status(thm)],[c_8338,c_48]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8436,plain,
% 3.54/0.98      ( v1_pre_topc(sK7) = iProver_top ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_8348,c_64,c_6892,c_6893,c_8342]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7044,plain,
% 3.54/0.98      ( l1_pre_topc(sK7) = iProver_top ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_6892,c_64]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_5,plain,
% 3.54/0.98      ( ~ l1_pre_topc(X0)
% 3.54/0.98      | ~ v1_pre_topc(X0)
% 3.54/0.98      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.54/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3918,plain,
% 3.54/0.98      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 3.54/0.98      | l1_pre_topc(X0) != iProver_top
% 3.54/0.98      | v1_pre_topc(X0) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7665,plain,
% 3.54/0.98      ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = sK7
% 3.54/0.98      | v1_pre_topc(sK7) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_7044,c_3918]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8441,plain,
% 3.54/0.98      ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = sK7 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_8436,c_7665]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_24,plain,
% 3.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.54/0.98      | X2 = X1
% 3.54/0.98      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f108]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3901,plain,
% 3.54/0.98      ( X0 = X1
% 3.54/0.98      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 3.54/0.98      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8451,plain,
% 3.54/0.98      ( g1_pre_topc(X0,X1) != sK7
% 3.54/0.98      | u1_struct_0(sK6) = X0
% 3.54/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_48,c_3901]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_22,plain,
% 3.54/0.98      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.54/0.98      | ~ l1_pre_topc(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f107]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6299,plain,
% 3.54/0.98      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
% 3.54/0.98      | ~ l1_pre_topc(sK6) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_22]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6304,plain,
% 3.54/0.98      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top
% 3.54/0.98      | l1_pre_topc(sK6) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_6299]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8452,plain,
% 3.54/0.98      ( g1_pre_topc(X0,X1) != sK7
% 3.54/0.98      | u1_struct_0(sK6) = X0
% 3.54/0.98      | m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_48,c_3901]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8721,plain,
% 3.54/0.98      ( u1_struct_0(sK6) = X0 | g1_pre_topc(X0,X1) != sK7 ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_8451,c_64,c_6304,c_6893,c_8452]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8722,plain,
% 3.54/0.98      ( g1_pre_topc(X0,X1) != sK7 | u1_struct_0(sK6) = X0 ),
% 3.54/0.98      inference(renaming,[status(thm)],[c_8721]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8728,plain,
% 3.54/0.98      ( u1_struct_0(sK7) = u1_struct_0(sK6) ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_8441,c_8722]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7133,plain,
% 3.54/0.98      ( l1_pre_topc(sK6) = iProver_top ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_6893,c_64]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_30,plain,
% 3.54/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.54/0.98      | ~ m1_pre_topc(X3,X4)
% 3.54/0.98      | ~ m1_pre_topc(X3,X1)
% 3.54/0.98      | ~ m1_pre_topc(X1,X4)
% 3.54/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.54/0.98      | ~ v1_funct_1(X0)
% 3.54/0.98      | v2_struct_0(X4)
% 3.54/0.98      | v2_struct_0(X2)
% 3.54/0.98      | ~ v2_pre_topc(X4)
% 3.54/0.98      | ~ v2_pre_topc(X2)
% 3.54/0.98      | ~ l1_pre_topc(X4)
% 3.54/0.98      | ~ l1_pre_topc(X2)
% 3.54/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f115]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_50,negated_conjecture,
% 3.54/0.98      ( v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
% 3.54/0.98      inference(cnf_transformation,[],[f139]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_961,plain,
% 3.54/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.54/0.98      | ~ m1_pre_topc(X0,X2)
% 3.54/0.98      | ~ m1_pre_topc(X1,X2)
% 3.54/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 3.54/0.98      | ~ v1_funct_1(X3)
% 3.54/0.98      | v2_struct_0(X4)
% 3.54/0.98      | v2_struct_0(X2)
% 3.54/0.98      | ~ v2_pre_topc(X4)
% 3.54/0.98      | ~ v2_pre_topc(X2)
% 3.54/0.98      | ~ l1_pre_topc(X4)
% 3.54/0.98      | ~ l1_pre_topc(X2)
% 3.54/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
% 3.54/0.98      | u1_struct_0(X4) != u1_struct_0(sK5)
% 3.54/0.98      | u1_struct_0(X1) != u1_struct_0(sK7)
% 3.54/0.98      | sK8 != X3 ),
% 3.54/0.98      inference(resolution_lifted,[status(thm)],[c_30,c_50]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_962,plain,
% 3.54/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.54/0.98      | ~ m1_pre_topc(X0,X2)
% 3.54/0.98      | ~ m1_pre_topc(X1,X2)
% 3.54/0.98      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.54/0.98      | ~ v1_funct_1(sK8)
% 3.54/0.98      | v2_struct_0(X2)
% 3.54/0.98      | v2_struct_0(X3)
% 3.54/0.98      | ~ v2_pre_topc(X2)
% 3.54/0.98      | ~ v2_pre_topc(X3)
% 3.54/0.98      | ~ l1_pre_topc(X2)
% 3.54/0.98      | ~ l1_pre_topc(X3)
% 3.54/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
% 3.54/0.98      | u1_struct_0(X3) != u1_struct_0(sK5)
% 3.54/0.98      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 3.54/0.98      inference(unflattening,[status(thm)],[c_961]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_51,negated_conjecture,
% 3.54/0.98      ( v1_funct_1(sK8) ),
% 3.54/0.98      inference(cnf_transformation,[],[f138]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_966,plain,
% 3.54/0.98      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.54/0.98      | ~ m1_pre_topc(X1,X2)
% 3.54/0.98      | ~ m1_pre_topc(X0,X2)
% 3.54/0.98      | ~ m1_pre_topc(X0,X1)
% 3.54/0.98      | v2_struct_0(X2)
% 3.54/0.98      | v2_struct_0(X3)
% 3.54/0.98      | ~ v2_pre_topc(X2)
% 3.54/0.98      | ~ v2_pre_topc(X3)
% 3.54/0.99      | ~ l1_pre_topc(X2)
% 3.54/0.99      | ~ l1_pre_topc(X3)
% 3.54/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
% 3.54/0.99      | u1_struct_0(X3) != u1_struct_0(sK5)
% 3.54/0.99      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_962,c_51]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_967,plain,
% 3.54/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ m1_pre_topc(X0,X2)
% 3.54/0.99      | ~ m1_pre_topc(X1,X2)
% 3.54/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.54/0.99      | v2_struct_0(X2)
% 3.54/0.99      | v2_struct_0(X3)
% 3.54/0.99      | ~ v2_pre_topc(X2)
% 3.54/0.99      | ~ v2_pre_topc(X3)
% 3.54/0.99      | ~ l1_pre_topc(X2)
% 3.54/0.99      | ~ l1_pre_topc(X3)
% 3.54/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
% 3.54/0.99      | u1_struct_0(X3) != u1_struct_0(sK5)
% 3.54/0.99      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_966]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_42,plain,
% 3.54/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ m1_pre_topc(X2,X0)
% 3.54/0.99      | m1_pre_topc(X2,X1)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f127]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_998,plain,
% 3.54/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ m1_pre_topc(X1,X2)
% 3.54/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.54/0.99      | v2_struct_0(X2)
% 3.54/0.99      | v2_struct_0(X3)
% 3.54/0.99      | ~ v2_pre_topc(X2)
% 3.54/0.99      | ~ v2_pre_topc(X3)
% 3.54/0.99      | ~ l1_pre_topc(X2)
% 3.54/0.99      | ~ l1_pre_topc(X3)
% 3.54/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
% 3.54/0.99      | u1_struct_0(X3) != u1_struct_0(sK5)
% 3.54/0.99      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 3.54/0.99      inference(forward_subsumption_resolution,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_967,c_42]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3875,plain,
% 3.54/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK8,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK8)
% 3.54/0.99      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.54/0.99      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.54/0.99      | m1_pre_topc(X2,X0) != iProver_top
% 3.54/0.99      | m1_pre_topc(X0,X3) != iProver_top
% 3.54/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.54/0.99      | v2_struct_0(X3) = iProver_top
% 3.54/0.99      | v2_struct_0(X1) = iProver_top
% 3.54/0.99      | v2_pre_topc(X3) != iProver_top
% 3.54/0.99      | v2_pre_topc(X1) != iProver_top
% 3.54/0.99      | l1_pre_topc(X3) != iProver_top
% 3.54/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_998]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5186,plain,
% 3.54/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k3_tmap_1(X2,sK5,X0,X1,sK8)
% 3.54/0.99      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.54/0.99      | m1_pre_topc(X0,X2) != iProver_top
% 3.54/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.54/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 3.54/0.99      | v2_struct_0(X2) = iProver_top
% 3.54/0.99      | v2_struct_0(sK5) = iProver_top
% 3.54/0.99      | v2_pre_topc(X2) != iProver_top
% 3.54/0.99      | v2_pre_topc(sK5) != iProver_top
% 3.54/0.99      | l1_pre_topc(X2) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK5) != iProver_top ),
% 3.54/0.99      inference(equality_resolution,[status(thm)],[c_3875]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_58,negated_conjecture,
% 3.54/0.99      ( ~ v2_struct_0(sK5) ),
% 3.54/0.99      inference(cnf_transformation,[],[f131]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_65,plain,
% 3.54/0.99      ( v2_struct_0(sK5) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_57,negated_conjecture,
% 3.54/0.99      ( v2_pre_topc(sK5) ),
% 3.54/0.99      inference(cnf_transformation,[],[f132]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_66,plain,
% 3.54/0.99      ( v2_pre_topc(sK5) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_56,negated_conjecture,
% 3.54/0.99      ( l1_pre_topc(sK5) ),
% 3.54/0.99      inference(cnf_transformation,[],[f133]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_67,plain,
% 3.54/0.99      ( l1_pre_topc(sK5) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5670,plain,
% 3.54/0.99      ( l1_pre_topc(X2) != iProver_top
% 3.54/0.99      | v2_struct_0(X2) = iProver_top
% 3.54/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 3.54/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.54/0.99      | m1_pre_topc(X0,X2) != iProver_top
% 3.54/0.99      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.54/0.99      | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k3_tmap_1(X2,sK5,X0,X1,sK8)
% 3.54/0.99      | v2_pre_topc(X2) != iProver_top ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_5186,c_65,c_66,c_67]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5671,plain,
% 3.54/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k3_tmap_1(X2,sK5,X0,X1,sK8)
% 3.54/0.99      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.54/0.99      | m1_pre_topc(X0,X2) != iProver_top
% 3.54/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.54/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 3.54/0.99      | v2_struct_0(X2) = iProver_top
% 3.54/0.99      | v2_pre_topc(X2) != iProver_top
% 3.54/0.99      | l1_pre_topc(X2) != iProver_top ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_5670]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5682,plain,
% 3.54/0.99      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK5,sK7,X0,sK8)
% 3.54/0.99      | m1_pre_topc(X0,sK7) != iProver_top
% 3.54/0.99      | m1_pre_topc(sK7,X1) != iProver_top
% 3.54/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
% 3.54/0.99      | v2_struct_0(X1) = iProver_top
% 3.54/0.99      | v2_pre_topc(X1) != iProver_top
% 3.54/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.54/0.99      inference(equality_resolution,[status(thm)],[c_5671]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_49,negated_conjecture,
% 3.54/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
% 3.54/0.99      inference(cnf_transformation,[],[f140]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_74,plain,
% 3.54/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6508,plain,
% 3.54/0.99      ( m1_pre_topc(sK7,X1) != iProver_top
% 3.54/0.99      | m1_pre_topc(X0,sK7) != iProver_top
% 3.54/0.99      | k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK5,sK7,X0,sK8)
% 3.54/0.99      | v2_struct_0(X1) = iProver_top
% 3.54/0.99      | v2_pre_topc(X1) != iProver_top
% 3.54/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_5682,c_74]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6509,plain,
% 3.54/0.99      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK5,sK7,X0,sK8)
% 3.54/0.99      | m1_pre_topc(X0,sK7) != iProver_top
% 3.54/0.99      | m1_pre_topc(sK7,X1) != iProver_top
% 3.54/0.99      | v2_struct_0(X1) = iProver_top
% 3.54/0.99      | v2_pre_topc(X1) != iProver_top
% 3.54/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_6508]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6521,plain,
% 3.54/0.99      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(X0,sK5,sK7,sK6,sK8)
% 3.54/0.99      | m1_pre_topc(sK7,X0) != iProver_top
% 3.54/0.99      | v2_struct_0(X0) = iProver_top
% 3.54/0.99      | v2_pre_topc(X0) != iProver_top
% 3.54/0.99      | l1_pre_topc(X0) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK6) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_6313,c_6509]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6561,plain,
% 3.54/0.99      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(sK4,sK5,sK7,sK6,sK8)
% 3.54/0.99      | v2_struct_0(sK4) = iProver_top
% 3.54/0.99      | v2_pre_topc(sK4) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK4) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK6) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_3886,c_6521]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_61,negated_conjecture,
% 3.54/0.99      ( ~ v2_struct_0(sK4) ),
% 3.54/0.99      inference(cnf_transformation,[],[f128]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_62,plain,
% 3.54/0.99      ( v2_struct_0(sK4) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_60,negated_conjecture,
% 3.54/0.99      ( v2_pre_topc(sK4) ),
% 3.54/0.99      inference(cnf_transformation,[],[f129]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_63,plain,
% 3.54/0.99      ( v2_pre_topc(sK4) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6652,plain,
% 3.54/0.99      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(sK4,sK5,sK7,sK6,sK8)
% 3.54/0.99      | l1_pre_topc(sK6) != iProver_top ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_6561,c_62,c_63,c_64]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_7139,plain,
% 3.54/0.99      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(sK4,sK5,sK7,sK6,sK8) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_7133,c_6652]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_29,plain,
% 3.54/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.54/0.99      | ~ m1_pre_topc(X3,X1)
% 3.54/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.54/0.99      | ~ v1_funct_1(X0)
% 3.54/0.99      | v2_struct_0(X1)
% 3.54/0.99      | v2_struct_0(X2)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ v2_pre_topc(X2)
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X2)
% 3.54/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.54/0.99      inference(cnf_transformation,[],[f114]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1012,plain,
% 3.54/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.54/0.99      | ~ v1_funct_1(X2)
% 3.54/0.99      | v2_struct_0(X1)
% 3.54/0.99      | v2_struct_0(X3)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ v2_pre_topc(X3)
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X3)
% 3.54/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
% 3.54/0.99      | u1_struct_0(X3) != u1_struct_0(sK5)
% 3.54/0.99      | u1_struct_0(X1) != u1_struct_0(sK7)
% 3.54/0.99      | sK8 != X2 ),
% 3.54/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_50]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1013,plain,
% 3.54/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.54/0.99      | ~ v1_funct_1(sK8)
% 3.54/0.99      | v2_struct_0(X1)
% 3.54/0.99      | v2_struct_0(X2)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ v2_pre_topc(X2)
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X2)
% 3.54/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK8,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK8,X0)
% 3.54/0.99      | u1_struct_0(X2) != u1_struct_0(sK5)
% 3.54/0.99      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 3.54/0.99      inference(unflattening,[status(thm)],[c_1012]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1017,plain,
% 3.54/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.54/0.99      | ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | v2_struct_0(X1)
% 3.54/0.99      | v2_struct_0(X2)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ v2_pre_topc(X2)
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X2)
% 3.54/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK8,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK8,X0)
% 3.54/0.99      | u1_struct_0(X2) != u1_struct_0(sK5)
% 3.54/0.99      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_1013,c_51]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1018,plain,
% 3.54/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.54/0.99      | v2_struct_0(X1)
% 3.54/0.99      | v2_struct_0(X2)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ v2_pre_topc(X2)
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X2)
% 3.54/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK8,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK8,X0)
% 3.54/0.99      | u1_struct_0(X2) != u1_struct_0(sK5)
% 3.54/0.99      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_1017]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3874,plain,
% 3.54/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK8,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK8,X2)
% 3.54/0.99      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.54/0.99      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.54/0.99      | m1_pre_topc(X2,X0) != iProver_top
% 3.54/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.54/0.99      | v2_struct_0(X0) = iProver_top
% 3.54/0.99      | v2_struct_0(X1) = iProver_top
% 3.54/0.99      | v2_pre_topc(X0) != iProver_top
% 3.54/0.99      | v2_pre_topc(X1) != iProver_top
% 3.54/0.99      | l1_pre_topc(X0) != iProver_top
% 3.54/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_1018]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_4995,plain,
% 3.54/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k2_tmap_1(X0,sK5,sK8,X1)
% 3.54/0.99      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.54/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.54/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 3.54/0.99      | v2_struct_0(X0) = iProver_top
% 3.54/0.99      | v2_struct_0(sK5) = iProver_top
% 3.54/0.99      | v2_pre_topc(X0) != iProver_top
% 3.54/0.99      | v2_pre_topc(sK5) != iProver_top
% 3.54/0.99      | l1_pre_topc(X0) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK5) != iProver_top ),
% 3.54/0.99      inference(equality_resolution,[status(thm)],[c_3874]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5158,plain,
% 3.54/0.99      ( l1_pre_topc(X0) != iProver_top
% 3.54/0.99      | v2_struct_0(X0) = iProver_top
% 3.54/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 3.54/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.54/0.99      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.54/0.99      | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k2_tmap_1(X0,sK5,sK8,X1)
% 3.54/0.99      | v2_pre_topc(X0) != iProver_top ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_4995,c_65,c_66,c_67]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5159,plain,
% 3.54/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k2_tmap_1(X0,sK5,sK8,X1)
% 3.54/0.99      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.54/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.54/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 3.54/0.99      | v2_struct_0(X0) = iProver_top
% 3.54/0.99      | v2_pre_topc(X0) != iProver_top
% 3.54/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_5158]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5169,plain,
% 3.54/0.99      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k2_tmap_1(sK7,sK5,sK8,X0)
% 3.54/0.99      | m1_pre_topc(X0,sK7) != iProver_top
% 3.54/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
% 3.54/0.99      | v2_struct_0(sK7) = iProver_top
% 3.54/0.99      | v2_pre_topc(sK7) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK7) != iProver_top ),
% 3.54/0.99      inference(equality_resolution,[status(thm)],[c_5159]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_53,negated_conjecture,
% 3.54/0.99      ( ~ v2_struct_0(sK7) ),
% 3.54/0.99      inference(cnf_transformation,[],[f136]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_70,plain,
% 3.54/0.99      ( v2_struct_0(sK7) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_71,plain,
% 3.54/0.99      ( m1_pre_topc(sK7,sK4) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6,plain,
% 3.54/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | v2_pre_topc(X0)
% 3.54/0.99      | ~ l1_pre_topc(X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_4767,plain,
% 3.54/0.99      ( ~ m1_pre_topc(sK7,X0)
% 3.54/0.99      | ~ v2_pre_topc(X0)
% 3.54/0.99      | v2_pre_topc(sK7)
% 3.54/0.99      | ~ l1_pre_topc(X0) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5487,plain,
% 3.54/0.99      ( ~ m1_pre_topc(sK7,sK4)
% 3.54/0.99      | ~ v2_pre_topc(sK4)
% 3.54/0.99      | v2_pre_topc(sK7)
% 3.54/0.99      | ~ l1_pre_topc(sK4) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_4767]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5488,plain,
% 3.54/0.99      ( m1_pre_topc(sK7,sK4) != iProver_top
% 3.54/0.99      | v2_pre_topc(sK4) != iProver_top
% 3.54/0.99      | v2_pre_topc(sK7) = iProver_top
% 3.54/0.99      | l1_pre_topc(sK4) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_5487]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5658,plain,
% 3.54/0.99      ( m1_pre_topc(X0,sK7) != iProver_top
% 3.54/0.99      | k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k2_tmap_1(sK7,sK5,sK8,X0)
% 3.54/0.99      | l1_pre_topc(sK7) != iProver_top ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_5169,c_63,c_64,c_70,c_71,c_74,c_5488]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5659,plain,
% 3.54/0.99      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k2_tmap_1(sK7,sK5,sK8,X0)
% 3.54/0.99      | m1_pre_topc(X0,sK7) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK7) != iProver_top ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_5658]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6416,plain,
% 3.54/0.99      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k2_tmap_1(sK7,sK5,sK8,sK6)
% 3.54/0.99      | l1_pre_topc(sK6) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK7) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_6313,c_5659]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_7140,plain,
% 3.54/0.99      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k2_tmap_1(sK7,sK5,sK8,sK6)
% 3.54/0.99      | l1_pre_topc(sK7) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_7133,c_6416]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_7146,plain,
% 3.54/0.99      ( k3_tmap_1(sK4,sK5,sK7,sK6,sK8) = k2_tmap_1(sK7,sK5,sK8,sK6)
% 3.54/0.99      | l1_pre_topc(sK7) != iProver_top ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_7139,c_7140]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_8048,plain,
% 3.54/0.99      ( k3_tmap_1(sK4,sK5,sK7,sK6,sK8) = k2_tmap_1(sK7,sK5,sK8,sK6) ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_7146,c_64,c_6892]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_44,negated_conjecture,
% 3.54/0.99      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
% 3.54/0.99      inference(cnf_transformation,[],[f145]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3890,plain,
% 3.54/0.99      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_45,negated_conjecture,
% 3.54/0.99      ( sK9 = sK10 ),
% 3.54/0.99      inference(cnf_transformation,[],[f144]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3962,plain,
% 3.54/0.99      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9) = iProver_top ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_3890,c_45]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_8052,plain,
% 3.54/0.99      ( r1_tmap_1(sK6,sK5,k2_tmap_1(sK7,sK5,sK8,sK6),sK9) = iProver_top ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_8048,c_3962]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_19,plain,
% 3.54/0.99      ( v3_pre_topc(X0,X1)
% 3.54/0.99      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.54/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/0.99      | ~ l1_pre_topc(X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_34,plain,
% 3.54/0.99      ( v1_tsep_1(X0,X1)
% 3.54/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.54/0.99      | ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f150]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_36,plain,
% 3.54/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/0.99      | ~ l1_pre_topc(X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f121]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_334,plain,
% 3.54/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.54/0.99      | v1_tsep_1(X0,X1)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X1) ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_34,c_36]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_335,plain,
% 3.54/0.99      ( v1_tsep_1(X0,X1)
% 3.54/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.54/0.99      | ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X1) ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_334]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_784,plain,
% 3.54/0.99      ( v1_tsep_1(X0,X1)
% 3.54/0.99      | ~ r2_hidden(X2,u1_pre_topc(X3))
% 3.54/0.99      | ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X3)
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | X1 != X3
% 3.54/0.99      | u1_struct_0(X0) != X2 ),
% 3.54/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_335]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_785,plain,
% 3.54/0.99      ( v1_tsep_1(X0,X1)
% 3.54/0.99      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
% 3.54/0.99      | ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X1) ),
% 3.54/0.99      inference(unflattening,[status(thm)],[c_784]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_789,plain,
% 3.54/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
% 3.54/0.99      | v1_tsep_1(X0,X1)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X1) ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_785,c_36]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_790,plain,
% 3.54/0.99      ( v1_tsep_1(X0,X1)
% 3.54/0.99      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
% 3.54/0.99      | ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X1) ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_789]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_40,plain,
% 3.54/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.54/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.54/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.54/0.99      | ~ v1_tsep_1(X4,X0)
% 3.54/0.99      | ~ m1_pre_topc(X4,X0)
% 3.54/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.54/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.54/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.54/0.99      | ~ v1_funct_1(X2)
% 3.54/0.99      | v2_struct_0(X1)
% 3.54/0.99      | v2_struct_0(X0)
% 3.54/0.99      | v2_struct_0(X4)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ v2_pre_topc(X0)
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X0) ),
% 3.54/0.99      inference(cnf_transformation,[],[f152]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_905,plain,
% 3.54/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.54/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.54/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.54/0.99      | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X6))
% 3.54/0.99      | ~ m1_pre_topc(X5,X6)
% 3.54/0.99      | ~ m1_pre_topc(X4,X0)
% 3.54/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.54/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.54/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.54/0.99      | ~ v1_funct_1(X2)
% 3.54/0.99      | v2_struct_0(X4)
% 3.54/0.99      | v2_struct_0(X1)
% 3.54/0.99      | v2_struct_0(X0)
% 3.54/0.99      | ~ v2_pre_topc(X6)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ v2_pre_topc(X0)
% 3.54/0.99      | ~ l1_pre_topc(X6)
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X0)
% 3.54/0.99      | X4 != X5
% 3.54/0.99      | X0 != X6 ),
% 3.54/0.99      inference(resolution_lifted,[status(thm)],[c_790,c_40]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_906,plain,
% 3.54/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.54/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.54/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.54/0.99      | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X0))
% 3.54/0.99      | ~ m1_pre_topc(X4,X0)
% 3.54/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.54/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.54/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.54/0.99      | ~ v1_funct_1(X2)
% 3.54/0.99      | v2_struct_0(X1)
% 3.54/0.99      | v2_struct_0(X4)
% 3.54/0.99      | v2_struct_0(X0)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ v2_pre_topc(X0)
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X0) ),
% 3.54/0.99      inference(unflattening,[status(thm)],[c_905]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_25,plain,
% 3.54/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.54/0.99      | m1_subset_1(X2,u1_struct_0(X1))
% 3.54/0.99      | v2_struct_0(X1)
% 3.54/0.99      | v2_struct_0(X0)
% 3.54/0.99      | ~ l1_pre_topc(X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f110]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_942,plain,
% 3.54/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.54/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.54/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.54/0.99      | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X0))
% 3.54/0.99      | ~ m1_pre_topc(X4,X0)
% 3.54/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.54/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.54/0.99      | ~ v1_funct_1(X2)
% 3.54/0.99      | v2_struct_0(X0)
% 3.54/0.99      | v2_struct_0(X1)
% 3.54/0.99      | v2_struct_0(X4)
% 3.54/0.99      | ~ v2_pre_topc(X0)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X0)
% 3.54/0.99      | ~ l1_pre_topc(X1) ),
% 3.54/0.99      inference(forward_subsumption_resolution,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_906,c_25]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1057,plain,
% 3.54/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.54/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.54/0.99      | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X0))
% 3.54/0.99      | ~ m1_pre_topc(X4,X0)
% 3.54/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.54/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.54/0.99      | ~ v1_funct_1(X2)
% 3.54/0.99      | v2_struct_0(X0)
% 3.54/0.99      | v2_struct_0(X1)
% 3.54/0.99      | v2_struct_0(X4)
% 3.54/0.99      | ~ v2_pre_topc(X0)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X0)
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.54/0.99      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.54/0.99      | sK8 != X2 ),
% 3.54/0.99      inference(resolution_lifted,[status(thm)],[c_942,c_50]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1058,plain,
% 3.54/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK8,X0),X3)
% 3.54/0.99      | r1_tmap_1(X2,X1,sK8,X3)
% 3.54/0.99      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X2))
% 3.54/0.99      | ~ m1_pre_topc(X0,X2)
% 3.54/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.54/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.54/0.99      | ~ v1_funct_1(sK8)
% 3.54/0.99      | v2_struct_0(X2)
% 3.54/0.99      | v2_struct_0(X1)
% 3.54/0.99      | v2_struct_0(X0)
% 3.54/0.99      | ~ v2_pre_topc(X2)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X2)
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.54/0.99      | u1_struct_0(X2) != u1_struct_0(sK7) ),
% 3.54/0.99      inference(unflattening,[status(thm)],[c_1057]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1062,plain,
% 3.54/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.54/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.54/0.99      | ~ m1_pre_topc(X0,X2)
% 3.54/0.99      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X2))
% 3.54/0.99      | r1_tmap_1(X2,X1,sK8,X3)
% 3.54/0.99      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK8,X0),X3)
% 3.54/0.99      | v2_struct_0(X2)
% 3.54/0.99      | v2_struct_0(X1)
% 3.54/0.99      | v2_struct_0(X0)
% 3.54/0.99      | ~ v2_pre_topc(X2)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X2)
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.54/0.99      | u1_struct_0(X2) != u1_struct_0(sK7) ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_1058,c_51]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1063,plain,
% 3.54/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK8,X0),X3)
% 3.54/0.99      | r1_tmap_1(X2,X1,sK8,X3)
% 3.54/0.99      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X2))
% 3.54/0.99      | ~ m1_pre_topc(X0,X2)
% 3.54/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.54/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.54/0.99      | v2_struct_0(X0)
% 3.54/0.99      | v2_struct_0(X1)
% 3.54/0.99      | v2_struct_0(X2)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ v2_pre_topc(X2)
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X2)
% 3.54/0.99      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.54/0.99      | u1_struct_0(X2) != u1_struct_0(sK7) ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_1062]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3873,plain,
% 3.54/0.99      ( u1_struct_0(X0) != u1_struct_0(sK5)
% 3.54/0.99      | u1_struct_0(X1) != u1_struct_0(sK7)
% 3.54/0.99      | r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK8,X2),X3) != iProver_top
% 3.54/0.99      | r1_tmap_1(X1,X0,sK8,X3) = iProver_top
% 3.54/0.99      | r2_hidden(u1_struct_0(X2),u1_pre_topc(X1)) != iProver_top
% 3.54/0.99      | m1_pre_topc(X2,X1) != iProver_top
% 3.54/0.99      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 3.54/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 3.54/0.99      | v2_struct_0(X0) = iProver_top
% 3.54/0.99      | v2_struct_0(X2) = iProver_top
% 3.54/0.99      | v2_struct_0(X1) = iProver_top
% 3.54/0.99      | v2_pre_topc(X0) != iProver_top
% 3.54/0.99      | v2_pre_topc(X1) != iProver_top
% 3.54/0.99      | l1_pre_topc(X0) != iProver_top
% 3.54/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_1063]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5015,plain,
% 3.54/0.99      ( u1_struct_0(X0) != u1_struct_0(sK5)
% 3.54/0.99      | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
% 3.54/0.99      | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
% 3.54/0.99      | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
% 3.54/0.99      | m1_pre_topc(X1,sK7) != iProver_top
% 3.54/0.99      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.54/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
% 3.54/0.99      | v2_struct_0(X1) = iProver_top
% 3.54/0.99      | v2_struct_0(X0) = iProver_top
% 3.54/0.99      | v2_struct_0(sK7) = iProver_top
% 3.54/0.99      | v2_pre_topc(X0) != iProver_top
% 3.54/0.99      | v2_pre_topc(sK7) != iProver_top
% 3.54/0.99      | l1_pre_topc(X0) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK7) != iProver_top ),
% 3.54/0.99      inference(equality_resolution,[status(thm)],[c_3873]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2692,plain,( X0 = X0 ),theory(equality) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_4398,plain,
% 3.54/0.99      ( u1_struct_0(sK7) = u1_struct_0(sK7) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_2692]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_4680,plain,
% 3.54/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK7,X1,sK8,X0),X2)
% 3.54/0.99      | r1_tmap_1(sK7,X1,sK8,X2)
% 3.54/0.99      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7))
% 3.54/0.99      | ~ m1_pre_topc(X0,sK7)
% 3.54/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.54/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X1))))
% 3.54/0.99      | v2_struct_0(X0)
% 3.54/0.99      | v2_struct_0(X1)
% 3.54/0.99      | v2_struct_0(sK7)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ v2_pre_topc(sK7)
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(sK7)
% 3.54/0.99      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.54/0.99      | u1_struct_0(sK7) != u1_struct_0(sK7) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_1063]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_4681,plain,
% 3.54/0.99      ( u1_struct_0(X0) != u1_struct_0(sK5)
% 3.54/0.99      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 3.54/0.99      | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
% 3.54/0.99      | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
% 3.54/0.99      | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
% 3.54/0.99      | m1_pre_topc(X1,sK7) != iProver_top
% 3.54/0.99      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.54/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
% 3.54/0.99      | v2_struct_0(X0) = iProver_top
% 3.54/0.99      | v2_struct_0(X1) = iProver_top
% 3.54/0.99      | v2_struct_0(sK7) = iProver_top
% 3.54/0.99      | v2_pre_topc(X0) != iProver_top
% 3.54/0.99      | v2_pre_topc(sK7) != iProver_top
% 3.54/0.99      | l1_pre_topc(X0) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK7) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_4680]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5537,plain,
% 3.54/0.99      ( v2_pre_topc(X0) != iProver_top
% 3.54/0.99      | u1_struct_0(X0) != u1_struct_0(sK5)
% 3.54/0.99      | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
% 3.54/0.99      | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
% 3.54/0.99      | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
% 3.54/0.99      | m1_pre_topc(X1,sK7) != iProver_top
% 3.54/0.99      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.54/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
% 3.54/0.99      | v2_struct_0(X1) = iProver_top
% 3.54/0.99      | v2_struct_0(X0) = iProver_top
% 3.54/0.99      | l1_pre_topc(X0) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK7) != iProver_top ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_5015,c_63,c_64,c_70,c_71,c_4398,c_4681,c_5488]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5538,plain,
% 3.54/0.99      ( u1_struct_0(X0) != u1_struct_0(sK5)
% 3.54/0.99      | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
% 3.54/0.99      | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
% 3.54/0.99      | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
% 3.54/0.99      | m1_pre_topc(X1,sK7) != iProver_top
% 3.54/0.99      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.54/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
% 3.54/0.99      | v2_struct_0(X1) = iProver_top
% 3.54/0.99      | v2_struct_0(X0) = iProver_top
% 3.54/0.99      | v2_pre_topc(X0) != iProver_top
% 3.54/0.99      | l1_pre_topc(X0) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK7) != iProver_top ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_5537]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5555,plain,
% 3.54/0.99      ( r1_tmap_1(X0,sK5,k2_tmap_1(sK7,sK5,sK8,X0),X1) != iProver_top
% 3.54/0.99      | r1_tmap_1(sK7,sK5,sK8,X1) = iProver_top
% 3.54/0.99      | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
% 3.54/0.99      | m1_pre_topc(X0,sK7) != iProver_top
% 3.54/0.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.54/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
% 3.54/0.99      | v2_struct_0(X0) = iProver_top
% 3.54/0.99      | v2_struct_0(sK5) = iProver_top
% 3.54/0.99      | v2_pre_topc(sK5) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK5) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK7) != iProver_top ),
% 3.54/0.99      inference(equality_resolution,[status(thm)],[c_5538]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5853,plain,
% 3.54/0.99      ( v2_struct_0(X0) = iProver_top
% 3.54/0.99      | r1_tmap_1(X0,sK5,k2_tmap_1(sK7,sK5,sK8,X0),X1) != iProver_top
% 3.54/0.99      | r1_tmap_1(sK7,sK5,sK8,X1) = iProver_top
% 3.54/0.99      | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
% 3.54/0.99      | m1_pre_topc(X0,sK7) != iProver_top
% 3.54/0.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK7) != iProver_top ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_5555,c_65,c_66,c_67,c_74]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5854,plain,
% 3.54/0.99      ( r1_tmap_1(X0,sK5,k2_tmap_1(sK7,sK5,sK8,X0),X1) != iProver_top
% 3.54/0.99      | r1_tmap_1(sK7,sK5,sK8,X1) = iProver_top
% 3.54/0.99      | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
% 3.54/0.99      | m1_pre_topc(X0,sK7) != iProver_top
% 3.54/0.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.54/0.99      | v2_struct_0(X0) = iProver_top
% 3.54/0.99      | l1_pre_topc(sK7) != iProver_top ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_5853]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_8060,plain,
% 3.54/0.99      ( r1_tmap_1(sK7,sK5,sK8,sK9) = iProver_top
% 3.54/0.99      | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top
% 3.54/0.99      | m1_pre_topc(sK6,sK7) != iProver_top
% 3.54/0.99      | m1_subset_1(sK9,u1_struct_0(sK6)) != iProver_top
% 3.54/0.99      | v2_struct_0(sK6) = iProver_top
% 3.54/0.99      | l1_pre_topc(sK7) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_8052,c_5854]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_55,negated_conjecture,
% 3.54/0.99      ( ~ v2_struct_0(sK6) ),
% 3.54/0.99      inference(cnf_transformation,[],[f134]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_68,plain,
% 3.54/0.99      ( v2_struct_0(sK6) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_43,negated_conjecture,
% 3.54/0.99      ( ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
% 3.54/0.99      inference(cnf_transformation,[],[f146]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_78,plain,
% 3.54/0.99      ( r1_tmap_1(sK7,sK5,sK8,sK9) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_46,negated_conjecture,
% 3.54/0.99      ( m1_subset_1(sK10,u1_struct_0(sK6)) ),
% 3.54/0.99      inference(cnf_transformation,[],[f143]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3889,plain,
% 3.54/0.99      ( m1_subset_1(sK10,u1_struct_0(sK6)) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3949,plain,
% 3.54/0.99      ( m1_subset_1(sK9,u1_struct_0(sK6)) = iProver_top ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_3889,c_45]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_8202,plain,
% 3.54/0.99      ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_8060,c_64,c_68,c_78,c_3949,c_6313,c_6892,c_6893]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_8807,plain,
% 3.54/0.99      ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) != iProver_top ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_8728,c_8202]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_8822,plain,
% 3.54/0.99      ( ~ r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) ),
% 3.54/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_8807]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6903,plain,
% 3.54/0.99      ( ~ l1_pre_topc(sK4) | l1_pre_topc(sK7) ),
% 3.54/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6892]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(contradiction,plain,
% 3.54/0.99      ( $false ),
% 3.54/0.99      inference(minisat,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_9570,c_8822,c_6903,c_5487,c_52,c_59,c_60]) ).
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.54/0.99  
% 3.54/0.99  ------                               Statistics
% 3.54/0.99  
% 3.54/0.99  ------ General
% 3.54/0.99  
% 3.54/0.99  abstr_ref_over_cycles:                  0
% 3.54/0.99  abstr_ref_under_cycles:                 0
% 3.54/0.99  gc_basic_clause_elim:                   0
% 3.54/0.99  forced_gc_time:                         0
% 3.54/0.99  parsing_time:                           0.014
% 3.54/0.99  unif_index_cands_time:                  0.
% 3.54/0.99  unif_index_add_time:                    0.
% 3.54/0.99  orderings_time:                         0.
% 3.54/0.99  out_proof_time:                         0.016
% 3.54/0.99  total_time:                             0.251
% 3.54/0.99  num_of_symbols:                         65
% 3.54/0.99  num_of_terms:                           5861
% 3.54/0.99  
% 3.54/0.99  ------ Preprocessing
% 3.54/0.99  
% 3.54/0.99  num_of_splits:                          0
% 3.54/0.99  num_of_split_atoms:                     0
% 3.54/0.99  num_of_reused_defs:                     0
% 3.54/0.99  num_eq_ax_congr_red:                    26
% 3.54/0.99  num_of_sem_filtered_clauses:            1
% 3.54/0.99  num_of_subtypes:                        0
% 3.54/0.99  monotx_restored_types:                  0
% 3.54/0.99  sat_num_of_epr_types:                   0
% 3.54/0.99  sat_num_of_non_cyclic_types:            0
% 3.54/0.99  sat_guarded_non_collapsed_types:        0
% 3.54/0.99  num_pure_diseq_elim:                    0
% 3.54/0.99  simp_replaced_by:                       0
% 3.54/0.99  res_preprocessed:                       261
% 3.54/0.99  prep_upred:                             0
% 3.54/0.99  prep_unflattend:                        26
% 3.54/0.99  smt_new_axioms:                         0
% 3.54/0.99  pred_elim_cands:                        10
% 3.54/0.99  pred_elim:                              4
% 3.54/0.99  pred_elim_cl:                           6
% 3.54/0.99  pred_elim_cycles:                       8
% 3.54/0.99  merged_defs:                            8
% 3.54/0.99  merged_defs_ncl:                        0
% 3.54/0.99  bin_hyper_res:                          8
% 3.54/0.99  prep_cycles:                            4
% 3.54/0.99  pred_elim_time:                         0.033
% 3.54/0.99  splitting_time:                         0.
% 3.54/0.99  sem_filter_time:                        0.
% 3.54/0.99  monotx_time:                            0.
% 3.54/0.99  subtype_inf_time:                       0.
% 3.54/0.99  
% 3.54/0.99  ------ Problem properties
% 3.54/0.99  
% 3.54/0.99  clauses:                                53
% 3.54/0.99  conjectures:                            17
% 3.54/0.99  epr:                                    19
% 3.54/0.99  horn:                                   42
% 3.54/0.99  ground:                                 17
% 3.54/0.99  unary:                                  18
% 3.54/0.99  binary:                                 9
% 3.54/0.99  lits:                                   178
% 3.54/0.99  lits_eq:                                18
% 3.54/0.99  fd_pure:                                0
% 3.54/0.99  fd_pseudo:                              0
% 3.54/0.99  fd_cond:                                0
% 3.54/0.99  fd_pseudo_cond:                         3
% 3.54/0.99  ac_symbols:                             0
% 3.54/0.99  
% 3.54/0.99  ------ Propositional Solver
% 3.54/0.99  
% 3.54/0.99  prop_solver_calls:                      28
% 3.54/0.99  prop_fast_solver_calls:                 2556
% 3.54/0.99  smt_solver_calls:                       0
% 3.54/0.99  smt_fast_solver_calls:                  0
% 3.54/0.99  prop_num_of_clauses:                    2577
% 3.54/0.99  prop_preprocess_simplified:             9737
% 3.54/0.99  prop_fo_subsumed:                       56
% 3.54/0.99  prop_solver_time:                       0.
% 3.54/0.99  smt_solver_time:                        0.
% 3.54/0.99  smt_fast_solver_time:                   0.
% 3.54/0.99  prop_fast_solver_time:                  0.
% 3.54/0.99  prop_unsat_core_time:                   0.
% 3.54/0.99  
% 3.54/0.99  ------ QBF
% 3.54/0.99  
% 3.54/0.99  qbf_q_res:                              0
% 3.54/0.99  qbf_num_tautologies:                    0
% 3.54/0.99  qbf_prep_cycles:                        0
% 3.54/0.99  
% 3.54/0.99  ------ BMC1
% 3.54/0.99  
% 3.54/0.99  bmc1_current_bound:                     -1
% 3.54/0.99  bmc1_last_solved_bound:                 -1
% 3.54/0.99  bmc1_unsat_core_size:                   -1
% 3.54/0.99  bmc1_unsat_core_parents_size:           -1
% 3.54/0.99  bmc1_merge_next_fun:                    0
% 3.54/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.54/0.99  
% 3.54/0.99  ------ Instantiation
% 3.54/0.99  
% 3.54/0.99  inst_num_of_clauses:                    674
% 3.54/0.99  inst_num_in_passive:                    212
% 3.54/0.99  inst_num_in_active:                     399
% 3.54/0.99  inst_num_in_unprocessed:                62
% 3.54/0.99  inst_num_of_loops:                      425
% 3.54/0.99  inst_num_of_learning_restarts:          0
% 3.54/0.99  inst_num_moves_active_passive:          22
% 3.54/0.99  inst_lit_activity:                      0
% 3.54/0.99  inst_lit_activity_moves:                0
% 3.54/0.99  inst_num_tautologies:                   0
% 3.54/0.99  inst_num_prop_implied:                  0
% 3.54/0.99  inst_num_existing_simplified:           0
% 3.54/0.99  inst_num_eq_res_simplified:             0
% 3.54/0.99  inst_num_child_elim:                    0
% 3.54/0.99  inst_num_of_dismatching_blockings:      285
% 3.54/0.99  inst_num_of_non_proper_insts:           1137
% 3.54/0.99  inst_num_of_duplicates:                 0
% 3.54/0.99  inst_inst_num_from_inst_to_res:         0
% 3.54/0.99  inst_dismatching_checking_time:         0.
% 3.54/0.99  
% 3.54/0.99  ------ Resolution
% 3.54/0.99  
% 3.54/0.99  res_num_of_clauses:                     0
% 3.54/0.99  res_num_in_passive:                     0
% 3.54/0.99  res_num_in_active:                      0
% 3.54/0.99  res_num_of_loops:                       265
% 3.54/0.99  res_forward_subset_subsumed:            106
% 3.54/0.99  res_backward_subset_subsumed:           0
% 3.54/0.99  res_forward_subsumed:                   0
% 3.54/0.99  res_backward_subsumed:                  0
% 3.54/0.99  res_forward_subsumption_resolution:     3
% 3.54/0.99  res_backward_subsumption_resolution:    0
% 3.54/0.99  res_clause_to_clause_subsumption:       613
% 3.54/0.99  res_orphan_elimination:                 0
% 3.54/0.99  res_tautology_del:                      105
% 3.54/0.99  res_num_eq_res_simplified:              0
% 3.54/0.99  res_num_sel_changes:                    0
% 3.54/0.99  res_moves_from_active_to_pass:          0
% 3.54/0.99  
% 3.54/0.99  ------ Superposition
% 3.54/0.99  
% 3.54/0.99  sup_time_total:                         0.
% 3.54/0.99  sup_time_generating:                    0.
% 3.54/0.99  sup_time_sim_full:                      0.
% 3.54/0.99  sup_time_sim_immed:                     0.
% 3.54/0.99  
% 3.54/0.99  sup_num_of_clauses:                     131
% 3.54/0.99  sup_num_in_active:                      71
% 3.54/0.99  sup_num_in_passive:                     60
% 3.54/0.99  sup_num_of_loops:                       84
% 3.54/0.99  sup_fw_superposition:                   55
% 3.54/0.99  sup_bw_superposition:                   42
% 3.54/0.99  sup_immediate_simplified:               22
% 3.54/0.99  sup_given_eliminated:                   0
% 3.54/0.99  comparisons_done:                       0
% 3.54/0.99  comparisons_avoided:                    0
% 3.54/0.99  
% 3.54/0.99  ------ Simplifications
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  sim_fw_subset_subsumed:                 4
% 3.54/0.99  sim_bw_subset_subsumed:                 7
% 3.54/0.99  sim_fw_subsumed:                        2
% 3.54/0.99  sim_bw_subsumed:                        0
% 3.54/0.99  sim_fw_subsumption_res:                 1
% 3.54/0.99  sim_bw_subsumption_res:                 0
% 3.54/0.99  sim_tautology_del:                      8
% 3.54/0.99  sim_eq_tautology_del:                   4
% 3.54/0.99  sim_eq_res_simp:                        0
% 3.54/0.99  sim_fw_demodulated:                     1
% 3.54/0.99  sim_bw_demodulated:                     11
% 3.54/0.99  sim_light_normalised:                   17
% 3.54/0.99  sim_joinable_taut:                      0
% 3.54/0.99  sim_joinable_simp:                      0
% 3.54/0.99  sim_ac_normalised:                      0
% 3.54/0.99  sim_smt_subsumption:                    0
% 3.54/0.99  
%------------------------------------------------------------------------------
