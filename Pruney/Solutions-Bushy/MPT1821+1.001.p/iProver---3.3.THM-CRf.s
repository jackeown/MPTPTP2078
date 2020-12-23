%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1821+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:33 EST 2020

% Result     : Theorem 39.80s
% Output     : CNFRefutation 39.80s
% Verified   : 
% Statistics : Number of formulae       :  358 (1542 expanded)
%              Number of clauses        :  233 ( 324 expanded)
%              Number of leaves         :   26 ( 469 expanded)
%              Depth                    :   21
%              Number of atoms          : 2491 (27508 expanded)
%              Number of equality atoms :  231 (1211 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal clause size      :   40 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(X2,X0,X1)
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( sP2(X3,X2,X1,X0)
    <=> ! [X4] :
          ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
            & v5_pre_topc(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X3)
            & v1_funct_2(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
            & v1_funct_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2))) )
          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
          | ~ v1_funct_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f48,plain,(
    ! [X3,X2,X1,X0] :
      ( ( sP2(X3,X2,X1,X0)
        | ? [X4] :
            ( ( ~ m1_subset_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
              | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X3)
              | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
              | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2))) )
            & m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
            & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
            & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
            & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
            & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
            & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
            & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
            & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
            & v1_funct_1(X4) ) )
      & ( ! [X4] :
            ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
              & v5_pre_topc(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X3)
              & v1_funct_2(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
              & v1_funct_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2))) )
            | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
            | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
            | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
            | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
            | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
            | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
            | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
            | ~ v1_funct_1(X4) )
        | ~ sP2(X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ m1_subset_1(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
              | ~ v5_pre_topc(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),k1_tsep_1(X3,X2,X1),X0)
              | ~ v1_funct_2(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
              | ~ v1_funct_1(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1))) )
            & m1_subset_1(k2_tmap_1(X3,X0,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v5_pre_topc(k2_tmap_1(X3,X0,X4,X1),X1,X0)
            & v1_funct_2(k2_tmap_1(X3,X0,X4,X1),u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(k2_tmap_1(X3,X0,X4,X1))
            & m1_subset_1(k2_tmap_1(X3,X0,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            & v5_pre_topc(k2_tmap_1(X3,X0,X4,X2),X2,X0)
            & v1_funct_2(k2_tmap_1(X3,X0,X4,X2),u1_struct_0(X2),u1_struct_0(X0))
            & v1_funct_1(k2_tmap_1(X3,X0,X4,X2))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
            & v1_funct_1(X4) ) )
      & ( ! [X5] :
            ( ( m1_subset_1(k2_tmap_1(X3,X0,X5,k1_tsep_1(X3,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
              & v5_pre_topc(k2_tmap_1(X3,X0,X5,k1_tsep_1(X3,X2,X1)),k1_tsep_1(X3,X2,X1),X0)
              & v1_funct_2(k2_tmap_1(X3,X0,X5,k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
              & v1_funct_1(k2_tmap_1(X3,X0,X5,k1_tsep_1(X3,X2,X1))) )
            | ~ m1_subset_1(k2_tmap_1(X3,X0,X5,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X3,X0,X5,X1),X1,X0)
            | ~ v1_funct_2(k2_tmap_1(X3,X0,X5,X1),u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X3,X0,X5,X1))
            | ~ m1_subset_1(k2_tmap_1(X3,X0,X5,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X3,X0,X5,X2),X2,X0)
            | ~ v1_funct_2(k2_tmap_1(X3,X0,X5,X2),u1_struct_0(X2),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X3,X0,X5,X2))
            | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
            | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X0))
            | ~ v1_funct_1(X5) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),k1_tsep_1(X3,X2,X1),X0)
            | ~ v1_funct_2(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1))) )
          & m1_subset_1(k2_tmap_1(X3,X0,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X4,X1),X1,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X4,X1),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X4,X1))
          & m1_subset_1(k2_tmap_1(X3,X0,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X4,X2),X2,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X4,X2),u1_struct_0(X2),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X4,X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( ( ~ m1_subset_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
          | ~ v5_pre_topc(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),k1_tsep_1(X3,X2,X1),X0)
          | ~ v1_funct_2(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
          | ~ v1_funct_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1))) )
        & m1_subset_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v5_pre_topc(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1),X1,X0)
        & v1_funct_2(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1))
        & m1_subset_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        & v5_pre_topc(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2),X2,X0)
        & v1_funct_2(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0))
        & v1_funct_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2))
        & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        & v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X0))
        & v1_funct_1(sK4(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ( ( ~ m1_subset_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),k1_tsep_1(X3,X2,X1),X0)
            | ~ v1_funct_2(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1))) )
          & m1_subset_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1),X1,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1))
          & m1_subset_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2),X2,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2))
          & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(sK4(X0,X1,X2,X3)) ) )
      & ( ! [X5] :
            ( ( m1_subset_1(k2_tmap_1(X3,X0,X5,k1_tsep_1(X3,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
              & v5_pre_topc(k2_tmap_1(X3,X0,X5,k1_tsep_1(X3,X2,X1)),k1_tsep_1(X3,X2,X1),X0)
              & v1_funct_2(k2_tmap_1(X3,X0,X5,k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
              & v1_funct_1(k2_tmap_1(X3,X0,X5,k1_tsep_1(X3,X2,X1))) )
            | ~ m1_subset_1(k2_tmap_1(X3,X0,X5,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X3,X0,X5,X1),X1,X0)
            | ~ v1_funct_2(k2_tmap_1(X3,X0,X5,X1),u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X3,X0,X5,X1))
            | ~ m1_subset_1(k2_tmap_1(X3,X0,X5,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X3,X0,X5,X2),X2,X0)
            | ~ v1_funct_2(k2_tmap_1(X3,X0,X5,X2),u1_struct_0(X2),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X3,X0,X5,X2))
            | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
            | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X0))
            | ~ v1_funct_1(X5) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | ~ m1_subset_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),k1_tsep_1(X3,X2,X1),X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f40,plain,(
    ! [X3,X0,X2,X1] :
      ( sP3(X3,X0,X2,X1)
    <=> ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
            & v5_pre_topc(X4,X0,X3)
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
            & v1_funct_1(X4) )
          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
          | ~ v1_funct_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f59,plain,(
    ! [X3,X0,X2,X1] :
      ( ( sP3(X3,X0,X2,X1)
        | ? [X4] :
            ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
              | ~ v5_pre_topc(X4,X0,X3)
              | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
              | ~ v1_funct_1(X4) )
            & m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
            & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
            & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
            & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
            & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
            & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
            & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
            & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
            & v1_funct_1(X4) ) )
      & ( ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
              & v5_pre_topc(X4,X0,X3)
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
              & v1_funct_1(X4) )
            | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
            | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
            | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
            | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
            | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
            | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
            | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
            | ~ v1_funct_1(X4) )
        | ~ sP3(X3,X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v5_pre_topc(X4,X1,X0)
              | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X4) )
            & m1_subset_1(k2_tmap_1(X1,X0,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            & v5_pre_topc(k2_tmap_1(X1,X0,X4,X2),X2,X0)
            & v1_funct_2(k2_tmap_1(X1,X0,X4,X2),u1_struct_0(X2),u1_struct_0(X0))
            & v1_funct_1(k2_tmap_1(X1,X0,X4,X2))
            & m1_subset_1(k2_tmap_1(X1,X0,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
            & v5_pre_topc(k2_tmap_1(X1,X0,X4,X3),X3,X0)
            & v1_funct_2(k2_tmap_1(X1,X0,X4,X3),u1_struct_0(X3),u1_struct_0(X0))
            & v1_funct_1(k2_tmap_1(X1,X0,X4,X3))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(X4) ) )
      & ( ! [X5] :
            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v5_pre_topc(X5,X1,X0)
              & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X5) )
            | ~ m1_subset_1(k2_tmap_1(X1,X0,X5,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X1,X0,X5,X2),X2,X0)
            | ~ v1_funct_2(k2_tmap_1(X1,X0,X5,X2),u1_struct_0(X2),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X1,X0,X5,X2))
            | ~ m1_subset_1(k2_tmap_1(X1,X0,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X1,X0,X5,X3),X3,X0)
            | ~ v1_funct_2(k2_tmap_1(X1,X0,X5,X3),u1_struct_0(X3),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X1,X0,X5,X3))
            | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(X5) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f59])).

fof(f61,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v5_pre_topc(X4,X1,X0)
            | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(X4) )
          & m1_subset_1(k2_tmap_1(X1,X0,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X1,X0,X4,X2),X2,X0)
          & v1_funct_2(k2_tmap_1(X1,X0,X4,X2),u1_struct_0(X2),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X1,X0,X4,X2))
          & m1_subset_1(k2_tmap_1(X1,X0,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X1,X0,X4,X3),X3,X0)
          & v1_funct_2(k2_tmap_1(X1,X0,X4,X3),u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X1,X0,X4,X3))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( ( ~ m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          | ~ v5_pre_topc(sK6(X0,X1,X2,X3),X1,X0)
          | ~ v1_funct_2(sK6(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
          | ~ v1_funct_1(sK6(X0,X1,X2,X3)) )
        & m1_subset_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        & v5_pre_topc(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2),X2,X0)
        & v1_funct_2(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0))
        & v1_funct_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2))
        & m1_subset_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        & v5_pre_topc(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3),X3,X0)
        & v1_funct_2(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3),u1_struct_0(X3),u1_struct_0(X0))
        & v1_funct_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3))
        & m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK6(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK6(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ( ( ~ m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v5_pre_topc(sK6(X0,X1,X2,X3),X1,X0)
            | ~ v1_funct_2(sK6(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(sK6(X0,X1,X2,X3)) )
          & m1_subset_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2),X2,X0)
          & v1_funct_2(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2))
          & m1_subset_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3),X3,X0)
          & v1_funct_2(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3),u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3))
          & m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(sK6(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(sK6(X0,X1,X2,X3)) ) )
      & ( ! [X5] :
            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v5_pre_topc(X5,X1,X0)
              & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X5) )
            | ~ m1_subset_1(k2_tmap_1(X1,X0,X5,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X1,X0,X5,X2),X2,X0)
            | ~ v1_funct_2(k2_tmap_1(X1,X0,X5,X2),u1_struct_0(X2),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X1,X0,X5,X2))
            | ~ m1_subset_1(k2_tmap_1(X1,X0,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X1,X0,X5,X3),X3,X0)
            | ~ v1_funct_2(k2_tmap_1(X1,X0,X5,X3),u1_struct_0(X3),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X1,X0,X5,X3))
            | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(X5) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f60,f61])).

fof(f125,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( v5_pre_topc(X5,X1,X0)
      | ~ m1_subset_1(k2_tmap_1(X1,X0,X5,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X1,X0,X5,X2),X2,X0)
      | ~ v1_funct_2(k2_tmap_1(X1,X0,X5,X2),u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X1,X0,X5,X2))
      | ~ m1_subset_1(k2_tmap_1(X1,X0,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X1,X0,X5,X3),X3,X0)
      | ~ v1_funct_2(k2_tmap_1(X1,X0,X5,X3),u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X1,X0,X5,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X5)
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,conjecture,(
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
             => ( k1_tsep_1(X0,X1,X2) = X0
               => ( r3_tsep_1(X0,X1,X2)
                <=> ( ! [X3] :
                        ( ( l1_pre_topc(X3)
                          & v2_pre_topc(X3)
                          & ~ v2_struct_0(X3) )
                       => ! [X4] :
                            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                              & v1_funct_1(X4) )
                           => ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                                & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                                & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                                & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                                & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                                & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                                & v1_funct_1(k2_tmap_1(X0,X3,X4,X1)) )
                             => ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                                & v5_pre_topc(X4,X0,X3)
                                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                                & v1_funct_1(X4) ) ) ) )
                    & r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
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
               => ( k1_tsep_1(X0,X1,X2) = X0
                 => ( r3_tsep_1(X0,X1,X2)
                  <=> ( ! [X3] :
                          ( ( l1_pre_topc(X3)
                            & v2_pre_topc(X3)
                            & ~ v2_struct_0(X3) )
                         => ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                                & v1_funct_1(X4) )
                             => ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                  & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                                  & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                                  & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                                  & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                                  & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                                  & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                                  & v1_funct_1(k2_tmap_1(X0,X3,X4,X1)) )
                               => ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                                  & v5_pre_topc(X4,X0,X3)
                                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                                  & v1_funct_1(X4) ) ) ) )
                      & r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                            & v5_pre_topc(X4,X0,X3)
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                            & v5_pre_topc(X4,X0,X3)
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( sP3(X3,X0,X2,X1)
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f34,f40])).

fof(f63,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ sP3(X3,X0,X2,X1)
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( sP3(X3,X0,X2,X1)
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(X0,X1,X2) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f64,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ sP3(X3,X0,X2,X1)
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( sP3(X3,X0,X2,X1)
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(X0,X1,X2) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f65,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ sP3(X3,X0,X2,X1)
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( sP3(X4,X0,X2,X1)
                      | ~ l1_pre_topc(X4)
                      | ~ v2_pre_topc(X4)
                      | v2_struct_0(X4) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(X0,X1,X2) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f64])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ sP3(X3,X0,X2,X1)
          & l1_pre_topc(X3)
          & v2_pre_topc(X3)
          & ~ v2_struct_0(X3) )
     => ( ~ sP3(sK10,X0,X2,X1)
        & l1_pre_topc(sK10)
        & v2_pre_topc(sK10)
        & ~ v2_struct_0(sK10) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ sP3(X3,X0,X2,X1)
                & l1_pre_topc(X3)
                & v2_pre_topc(X3)
                & ~ v2_struct_0(X3) )
            | ~ r1_tsep_1(X1,X2)
            | ~ r3_tsep_1(X0,X1,X2) )
          & ( ( ! [X4] :
                  ( sP3(X4,X0,X2,X1)
                  | ~ l1_pre_topc(X4)
                  | ~ v2_pre_topc(X4)
                  | v2_struct_0(X4) )
              & r1_tsep_1(X1,X2) )
            | r3_tsep_1(X0,X1,X2) )
          & k1_tsep_1(X0,X1,X2) = X0
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ( ? [X3] :
              ( ~ sP3(X3,X0,sK9,X1)
              & l1_pre_topc(X3)
              & v2_pre_topc(X3)
              & ~ v2_struct_0(X3) )
          | ~ r1_tsep_1(X1,sK9)
          | ~ r3_tsep_1(X0,X1,sK9) )
        & ( ( ! [X4] :
                ( sP3(X4,X0,sK9,X1)
                | ~ l1_pre_topc(X4)
                | ~ v2_pre_topc(X4)
                | v2_struct_0(X4) )
            & r1_tsep_1(X1,sK9) )
          | r3_tsep_1(X0,X1,sK9) )
        & k1_tsep_1(X0,X1,sK9) = X0
        & m1_pre_topc(sK9,X0)
        & ~ v2_struct_0(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ sP3(X3,X0,X2,X1)
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( sP3(X4,X0,X2,X1)
                      | ~ l1_pre_topc(X4)
                      | ~ v2_pre_topc(X4)
                      | v2_struct_0(X4) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(X0,X1,X2) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ sP3(X3,X0,X2,sK8)
                  & l1_pre_topc(X3)
                  & v2_pre_topc(X3)
                  & ~ v2_struct_0(X3) )
              | ~ r1_tsep_1(sK8,X2)
              | ~ r3_tsep_1(X0,sK8,X2) )
            & ( ( ! [X4] :
                    ( sP3(X4,X0,X2,sK8)
                    | ~ l1_pre_topc(X4)
                    | ~ v2_pre_topc(X4)
                    | v2_struct_0(X4) )
                & r1_tsep_1(sK8,X2) )
              | r3_tsep_1(X0,sK8,X2) )
            & k1_tsep_1(X0,sK8,X2) = X0
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK8,X0)
        & ~ v2_struct_0(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ sP3(X3,X0,X2,X1)
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2)
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( ( ! [X4] :
                        ( sP3(X4,X0,X2,X1)
                        | ~ l1_pre_topc(X4)
                        | ~ v2_pre_topc(X4)
                        | v2_struct_0(X4) )
                    & r1_tsep_1(X1,X2) )
                  | r3_tsep_1(X0,X1,X2) )
                & k1_tsep_1(X0,X1,X2) = X0
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ sP3(X3,sK7,X2,X1)
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(sK7,X1,X2) )
              & ( ( ! [X4] :
                      ( sP3(X4,sK7,X2,X1)
                      | ~ l1_pre_topc(X4)
                      | ~ v2_pre_topc(X4)
                      | v2_struct_0(X4) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(sK7,X1,X2) )
              & k1_tsep_1(sK7,X1,X2) = sK7
              & m1_pre_topc(X2,sK7)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK7)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK7)
      & v2_pre_topc(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ( ( ~ sP3(sK10,sK7,sK9,sK8)
        & l1_pre_topc(sK10)
        & v2_pre_topc(sK10)
        & ~ v2_struct_0(sK10) )
      | ~ r1_tsep_1(sK8,sK9)
      | ~ r3_tsep_1(sK7,sK8,sK9) )
    & ( ( ! [X4] :
            ( sP3(X4,sK7,sK9,sK8)
            | ~ l1_pre_topc(X4)
            | ~ v2_pre_topc(X4)
            | v2_struct_0(X4) )
        & r1_tsep_1(sK8,sK9) )
      | r3_tsep_1(sK7,sK8,sK9) )
    & k1_tsep_1(sK7,sK8,sK9) = sK7
    & m1_pre_topc(sK9,sK7)
    & ~ v2_struct_0(sK9)
    & m1_pre_topc(sK8,sK7)
    & ~ v2_struct_0(sK8)
    & l1_pre_topc(sK7)
    & v2_pre_topc(sK7)
    & ~ v2_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f65,f69,f68,f67,f66])).

fof(f146,plain,(
    k1_tsep_1(sK7,sK8,sK9) = sK7 ),
    inference(cnf_transformation,[],[f70])).

fof(f7,axiom,(
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( r4_tsep_1(X0,X3,X4)
                          & k1_tsep_1(X0,X3,X4) = X0 )
                       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f36,plain,(
    ! [X3,X0,X2,X4,X1] :
      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
      <=> sP0(X1,X4,X2,X0,X3) )
      | ~ sP1(X3,X0,X2,X4,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f35,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( sP0(X1,X4,X2,X0,X3)
    <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X3,X0,X2,X4,X1)
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f26,f36,f35])).

fof(f96,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X3,X0,X2,X4,X1)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f139,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f70])).

fof(f140,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f70])).

fof(f141,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f70])).

fof(f142,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f70])).

fof(f143,plain,(
    m1_pre_topc(sK8,sK7) ),
    inference(cnf_transformation,[],[f70])).

fof(f144,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f145,plain,(
    m1_pre_topc(sK9,sK7) ),
    inference(cnf_transformation,[],[f70])).

fof(f149,plain,
    ( ~ v2_struct_0(sK10)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ r3_tsep_1(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f150,plain,
    ( v2_pre_topc(sK10)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ r3_tsep_1(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f151,plain,
    ( l1_pre_topc(sK10)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ r3_tsep_1(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f152,plain,
    ( ~ sP3(sK10,sK7,sK9,sK8)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ r3_tsep_1(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f127,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | v1_funct_1(sK6(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | v1_funct_2(sK6(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | v1_funct_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | v1_funct_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | v1_funct_2(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3),u1_struct_0(X3),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | v5_pre_topc(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3),X3,X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | m1_subset_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | v1_funct_2(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f136,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | v5_pre_topc(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2),X2,X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | m1_subset_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & m1_pre_topc(X1,X0)
        & l1_pre_topc(X0) )
     => ( r4_tsep_1(X0,X1,X2)
       => r4_tsep_1(X0,X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r4_tsep_1(X0,X2,X1)
      | ~ r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r4_tsep_1(X0,X2,X1)
      | ~ r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X2,X1)
      | ~ r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( ( sP0(X1,X4,X2,X0,X3)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
        | ~ sP0(X1,X4,X2,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f46,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( ( sP0(X1,X4,X2,X0,X3)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
        | ~ sP0(X1,X4,X2,X0,X3) ) ) ),
    inference(flattening,[],[f45])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
        | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
        | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
        | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) )
      & ( ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
          & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f46])).

fof(f95,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
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
             => ( ( r4_tsep_1(X0,X1,X2)
                  & r1_tsep_1(X1,X2) )
              <=> r3_tsep_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r4_tsep_1(X0,X1,X2)
                  & r1_tsep_1(X1,X2) )
              <=> r3_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r4_tsep_1(X0,X1,X2)
                  & r1_tsep_1(X1,X2) )
              <=> r3_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( r4_tsep_1(X0,X1,X2)
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( r3_tsep_1(X0,X1,X2)
                  | ~ r4_tsep_1(X0,X1,X2)
                  | ~ r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( r4_tsep_1(X0,X1,X2)
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( r3_tsep_1(X0,X1,X2)
                  | ~ r4_tsep_1(X0,X1,X2)
                  | ~ r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | ~ r4_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f42,plain,(
    ! [X3,X0,X2,X4,X1] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(X2,X0,X1)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X2) )
          | ~ sP0(X1,X4,X2,X0,X3) )
        & ( sP0(X1,X4,X2,X0,X3)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          | ~ v5_pre_topc(X2,X0,X1)
          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X3,X0,X2,X4,X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f43,plain,(
    ! [X3,X0,X2,X4,X1] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(X2,X0,X1)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X2) )
          | ~ sP0(X1,X4,X2,X0,X3) )
        & ( sP0(X1,X4,X2,X0,X3)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          | ~ v5_pre_topc(X2,X0,X1)
          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X3,X0,X2,X4,X1) ) ),
    inference(flattening,[],[f42])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
            & v5_pre_topc(X2,X1,X4)
            & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
            & v1_funct_1(X2) )
          | ~ sP0(X4,X3,X2,X1,X0) )
        & ( sP0(X4,X3,X2,X1,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
          | ~ v5_pre_topc(X2,X1,X4)
          | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f43])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X1,X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f147,plain,
    ( r1_tsep_1(sK8,sK9)
    | r3_tsep_1(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X1,X2)
      | ~ r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | ~ m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(sK6(X0,X1,X2,X3),X1,X0)
      | ~ v1_funct_2(sK6(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(sK6(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f8,axiom,(
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
             => ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ( l1_pre_topc(X3)
                        & v2_pre_topc(X3)
                        & ~ v2_struct_0(X3) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                         => ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                              & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                              & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                              & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                              & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                              & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                              & v1_funct_1(k2_tmap_1(X0,X3,X4,X1)) )
                           => ( m1_subset_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                              & v5_pre_topc(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X3)
                              & v1_funct_2(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                              & v1_funct_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2))) ) ) ) )
                  & r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v5_pre_topc(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X3)
                            & v1_funct_2(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2))) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v5_pre_topc(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X3)
                            & v1_funct_2(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2))) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( sP2(X3,X2,X1,X0)
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f28,f38])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ? [X3] :
                      ( ~ sP2(X3,X2,X1,X0)
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X3] :
                        ( sP2(X3,X2,X1,X0)
                        | ~ l1_pre_topc(X3)
                        | ~ v2_pre_topc(X3)
                        | v2_struct_0(X3) )
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ? [X3] :
                      ( ~ sP2(X3,X2,X1,X0)
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X3] :
                        ( sP2(X3,X2,X1,X0)
                        | ~ l1_pre_topc(X3)
                        | ~ v2_pre_topc(X3)
                        | v2_struct_0(X3) )
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ? [X3] :
                      ( ~ sP2(X3,X2,X1,X0)
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X4] :
                        ( sP2(X4,X2,X1,X0)
                        | ~ l1_pre_topc(X4)
                        | ~ v2_pre_topc(X4)
                        | v2_struct_0(X4) )
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ sP2(X3,X2,X1,X0)
          & l1_pre_topc(X3)
          & v2_pre_topc(X3)
          & ~ v2_struct_0(X3) )
     => ( ~ sP2(sK5(X0,X1,X2),X2,X1,X0)
        & l1_pre_topc(sK5(X0,X1,X2))
        & v2_pre_topc(sK5(X0,X1,X2))
        & ~ v2_struct_0(sK5(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ( ~ sP2(sK5(X0,X1,X2),X2,X1,X0)
                    & l1_pre_topc(sK5(X0,X1,X2))
                    & v2_pre_topc(sK5(X0,X1,X2))
                    & ~ v2_struct_0(sK5(X0,X1,X2)) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X4] :
                        ( sP2(X4,X2,X1,X0)
                        | ~ l1_pre_topc(X4)
                        | ~ v2_pre_topc(X4)
                        | v2_struct_0(X4) )
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f54,f55])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | ~ v2_struct_0(sK5(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | m1_subset_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | v5_pre_topc(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1),X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | v1_funct_2(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | m1_subset_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | v5_pre_topc(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2),X2,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | v1_funct_2(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | v1_funct_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | v1_funct_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | v1_funct_1(sK4(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f148,plain,(
    ! [X4] :
      ( sP3(X4,sK7,sK9,sK8)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | r3_tsep_1(sK7,sK8,sK9) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f77,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | ~ sP2(sK5(X0,X1,X2),X2,X1,X0)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | v2_pre_topc(sK5(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | l1_pre_topc(sK5(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1143,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | v1_funct_2(k2_tmap_1(X0_56,X1_56,X0_57,X2_56),u1_struct_0(X2_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ v1_funct_1(X0_57)
    | ~ l1_struct_0(X2_56)
    | ~ l1_struct_0(X1_56)
    | ~ l1_struct_0(X0_56) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_11337,plain,
    ( ~ v1_funct_2(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)))
    | v1_funct_2(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X0_56),u1_struct_0(X0_56),u1_struct_0(sK5(sK7,sK8,sK9)))
    | ~ m1_subset_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)))))
    | ~ v1_funct_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7))
    | ~ l1_struct_0(X0_56)
    | ~ l1_struct_0(sK5(sK7,sK8,sK9))
    | ~ l1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1143])).

cnf(c_83638,plain,
    ( ~ v1_funct_2(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)))
    | v1_funct_2(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_tsep_1(sK7,sK8,sK9)),u1_struct_0(k1_tsep_1(sK7,sK8,sK9)),u1_struct_0(sK5(sK7,sK8,sK9)))
    | ~ m1_subset_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)))))
    | ~ v1_funct_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7))
    | ~ l1_struct_0(sK5(sK7,sK8,sK9))
    | ~ l1_struct_0(k1_tsep_1(sK7,sK8,sK9))
    | ~ l1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_11337])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1142,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ v1_funct_1(X0_57)
    | v1_funct_1(k2_tmap_1(X0_56,X1_56,X0_57,X2_56))
    | ~ l1_struct_0(X2_56)
    | ~ l1_struct_0(X1_56)
    | ~ l1_struct_0(X0_56) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_11338,plain,
    ( ~ v1_funct_2(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)))
    | ~ m1_subset_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)))))
    | ~ v1_funct_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7))
    | v1_funct_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X0_56))
    | ~ l1_struct_0(X0_56)
    | ~ l1_struct_0(sK5(sK7,sK8,sK9))
    | ~ l1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1142])).

cnf(c_49496,plain,
    ( ~ v1_funct_2(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)))
    | ~ m1_subset_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)))))
    | ~ v1_funct_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7))
    | v1_funct_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_tsep_1(sK7,sK8,sK9)))
    | ~ l1_struct_0(sK5(sK7,sK8,sK9))
    | ~ l1_struct_0(k1_tsep_1(sK7,sK8,sK9))
    | ~ l1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_11338])).

cnf(c_7,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(k2_tmap_1(X1,X2,X0,X3),X3,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1140,plain,
    ( ~ v5_pre_topc(X0_57,X0_56,X1_56)
    | v5_pre_topc(k2_tmap_1(X0_56,X1_56,X0_57,X2_56),X2_56,X1_56)
    | ~ v1_funct_2(X0_57,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ m1_pre_topc(X2_56,X0_56)
    | ~ v2_pre_topc(X0_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v1_funct_1(X0_57)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X2_56) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_11339,plain,
    ( ~ v5_pre_topc(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7,sK5(sK7,sK8,sK9))
    | v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X0_56),X0_56,sK5(sK7,sK8,sK9))
    | ~ v1_funct_2(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)))
    | ~ m1_subset_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)))))
    | ~ m1_pre_topc(X0_56,sK7)
    | ~ v2_pre_topc(sK5(sK7,sK8,sK9))
    | ~ v2_pre_topc(sK7)
    | ~ v1_funct_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7))
    | ~ l1_pre_topc(sK5(sK7,sK8,sK9))
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(X0_56)
    | v2_struct_0(sK5(sK7,sK8,sK9))
    | v2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_44211,plain,
    ( ~ v5_pre_topc(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7,sK5(sK7,sK8,sK9))
    | v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_tsep_1(sK7,sK8,sK9)),k1_tsep_1(sK7,sK8,sK9),sK5(sK7,sK8,sK9))
    | ~ v1_funct_2(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)))
    | ~ m1_subset_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)))))
    | ~ m1_pre_topc(k1_tsep_1(sK7,sK8,sK9),sK7)
    | ~ v2_pre_topc(sK5(sK7,sK8,sK9))
    | ~ v2_pre_topc(sK7)
    | ~ v1_funct_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7))
    | ~ l1_pre_topc(sK5(sK7,sK8,sK9))
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK5(sK7,sK8,sK9))
    | v2_struct_0(k1_tsep_1(sK7,sK8,sK9))
    | v2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_11339])).

cnf(c_26,plain,
    ( sP2(X0,X1,X2,X3)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),k1_tsep_1(X3,X2,X1),X0)
    | ~ v1_funct_2(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1121,plain,
    ( sP2(X0_56,X1_56,X2_56,X3_56)
    | ~ v5_pre_topc(k2_tmap_1(X3_56,X0_56,sK4(X0_56,X1_56,X2_56,X3_56),k1_tsep_1(X3_56,X2_56,X1_56)),k1_tsep_1(X3_56,X2_56,X1_56),X0_56)
    | ~ v1_funct_2(k2_tmap_1(X3_56,X0_56,sK4(X0_56,X1_56,X2_56,X3_56),k1_tsep_1(X3_56,X2_56,X1_56)),u1_struct_0(k1_tsep_1(X3_56,X2_56,X1_56)),u1_struct_0(X0_56))
    | ~ m1_subset_1(k2_tmap_1(X3_56,X0_56,sK4(X0_56,X1_56,X2_56,X3_56),k1_tsep_1(X3_56,X2_56,X1_56)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_56,X2_56,X1_56)),u1_struct_0(X0_56))))
    | ~ v1_funct_1(k2_tmap_1(X3_56,X0_56,sK4(X0_56,X1_56,X2_56,X3_56),k1_tsep_1(X3_56,X2_56,X1_56))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_30978,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7)
    | ~ v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_tsep_1(sK7,sK8,sK9)),k1_tsep_1(sK7,sK8,sK9),sK5(sK7,sK8,sK9))
    | ~ v1_funct_2(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_tsep_1(sK7,sK8,sK9)),u1_struct_0(k1_tsep_1(sK7,sK8,sK9)),u1_struct_0(sK5(sK7,sK8,sK9)))
    | ~ m1_subset_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_tsep_1(sK7,sK8,sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK7,sK8,sK9)),u1_struct_0(sK5(sK7,sK8,sK9)))))
    | ~ v1_funct_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_tsep_1(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_1121])).

cnf(c_65,plain,
    ( ~ sP3(X0,X1,X2,X3)
    | v5_pre_topc(X4,X1,X0)
    | ~ v5_pre_topc(k2_tmap_1(X1,X0,X4,X2),X2,X0)
    | ~ v5_pre_topc(k2_tmap_1(X1,X0,X4,X3),X3,X0)
    | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k2_tmap_1(X1,X0,X4,X2),u1_struct_0(X2),u1_struct_0(X0))
    | ~ v1_funct_2(k2_tmap_1(X1,X0,X4,X3),u1_struct_0(X3),u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k2_tmap_1(X1,X0,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
    | ~ m1_subset_1(k2_tmap_1(X1,X0,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(k2_tmap_1(X1,X0,X4,X2))
    | ~ v1_funct_1(k2_tmap_1(X1,X0,X4,X3)) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1086,plain,
    ( ~ sP3(X0_56,X1_56,X2_56,X3_56)
    | v5_pre_topc(X0_57,X1_56,X0_56)
    | ~ v5_pre_topc(k2_tmap_1(X1_56,X0_56,X0_57,X2_56),X2_56,X0_56)
    | ~ v5_pre_topc(k2_tmap_1(X1_56,X0_56,X0_57,X3_56),X3_56,X0_56)
    | ~ v1_funct_2(X0_57,u1_struct_0(X1_56),u1_struct_0(X0_56))
    | ~ v1_funct_2(k2_tmap_1(X1_56,X0_56,X0_57,X2_56),u1_struct_0(X2_56),u1_struct_0(X0_56))
    | ~ v1_funct_2(k2_tmap_1(X1_56,X0_56,X0_57,X3_56),u1_struct_0(X3_56),u1_struct_0(X0_56))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(X0_56))))
    | ~ m1_subset_1(k2_tmap_1(X1_56,X0_56,X0_57,X2_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X0_56))))
    | ~ m1_subset_1(k2_tmap_1(X1_56,X0_56,X0_57,X3_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_56),u1_struct_0(X0_56))))
    | ~ v1_funct_1(X0_57)
    | ~ v1_funct_1(k2_tmap_1(X1_56,X0_56,X0_57,X2_56))
    | ~ v1_funct_1(k2_tmap_1(X1_56,X0_56,X0_57,X3_56)) ),
    inference(subtyping,[status(esa)],[c_65])).

cnf(c_11301,plain,
    ( ~ sP3(sK5(sK7,sK8,sK9),sK7,X0_56,X1_56)
    | v5_pre_topc(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7,sK5(sK7,sK8,sK9))
    | ~ v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X0_56),X0_56,sK5(sK7,sK8,sK9))
    | ~ v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X1_56),X1_56,sK5(sK7,sK8,sK9))
    | ~ v1_funct_2(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)))
    | ~ v1_funct_2(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X0_56),u1_struct_0(X0_56),u1_struct_0(sK5(sK7,sK8,sK9)))
    | ~ v1_funct_2(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X1_56),u1_struct_0(X1_56),u1_struct_0(sK5(sK7,sK8,sK9)))
    | ~ m1_subset_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)))))
    | ~ m1_subset_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK5(sK7,sK8,sK9)))))
    | ~ m1_subset_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X1_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(sK5(sK7,sK8,sK9)))))
    | ~ v1_funct_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7))
    | ~ v1_funct_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X0_56))
    | ~ v1_funct_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X1_56)) ),
    inference(instantiation,[status(thm)],[c_1086])).

cnf(c_22062,plain,
    ( ~ sP3(sK5(sK7,sK8,sK9),sK7,sK9,sK8)
    | v5_pre_topc(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7,sK5(sK7,sK8,sK9))
    | ~ v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8),sK8,sK5(sK7,sK8,sK9))
    | ~ v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK9),sK9,sK5(sK7,sK8,sK9))
    | ~ v1_funct_2(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)))
    | ~ v1_funct_2(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8),u1_struct_0(sK8),u1_struct_0(sK5(sK7,sK8,sK9)))
    | ~ v1_funct_2(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK9),u1_struct_0(sK9),u1_struct_0(sK5(sK7,sK8,sK9)))
    | ~ m1_subset_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)))))
    | ~ m1_subset_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK5(sK7,sK8,sK9)))))
    | ~ m1_subset_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK7,sK8,sK9)))))
    | ~ v1_funct_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7))
    | ~ v1_funct_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8))
    | ~ v1_funct_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK9)) ),
    inference(instantiation,[status(thm)],[c_11301])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1144,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | m1_subset_1(k2_tmap_1(X0_56,X1_56,X0_57,X2_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
    | ~ v1_funct_1(X0_57)
    | ~ l1_struct_0(X2_56)
    | ~ l1_struct_0(X1_56)
    | ~ l1_struct_0(X0_56) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_11336,plain,
    ( ~ v1_funct_2(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)))
    | ~ m1_subset_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)))))
    | m1_subset_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK5(sK7,sK8,sK9)))))
    | ~ v1_funct_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7))
    | ~ l1_struct_0(X0_56)
    | ~ l1_struct_0(sK5(sK7,sK8,sK9))
    | ~ l1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1144])).

cnf(c_19355,plain,
    ( ~ v1_funct_2(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)))
    | ~ m1_subset_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)))))
    | m1_subset_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_tsep_1(sK7,sK8,sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK7,sK8,sK9)),u1_struct_0(sK5(sK7,sK8,sK9)))))
    | ~ v1_funct_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7))
    | ~ l1_struct_0(sK5(sK7,sK8,sK9))
    | ~ l1_struct_0(k1_tsep_1(sK7,sK8,sK9))
    | ~ l1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_11336])).

cnf(c_74,negated_conjecture,
    ( k1_tsep_1(sK7,sK8,sK9) = sK7 ),
    inference(cnf_transformation,[],[f146])).

cnf(c_1079,negated_conjecture,
    ( k1_tsep_1(sK7,sK8,sK9) = sK7 ),
    inference(subtyping,[status(esa)],[c_74])).

cnf(c_25,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ r4_tsep_1(X1,X0,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | k1_tsep_1(X1,X0,X3) != X1 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1122,plain,
    ( sP1(X0_56,X1_56,X0_57,X2_56,X3_56)
    | ~ r4_tsep_1(X1_56,X0_56,X2_56)
    | ~ v1_funct_2(X0_57,u1_struct_0(X1_56),u1_struct_0(X3_56))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(X3_56))))
    | ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_pre_topc(X2_56,X1_56)
    | ~ v2_pre_topc(X3_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v1_funct_1(X0_57)
    | ~ l1_pre_topc(X3_56)
    | ~ l1_pre_topc(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X2_56)
    | v2_struct_0(X3_56)
    | k1_tsep_1(X1_56,X0_56,X2_56) != X1_56 ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2464,plain,
    ( k1_tsep_1(X0_56,X1_56,X2_56) != X0_56
    | sP1(X1_56,X0_56,X0_57,X2_56,X3_56) = iProver_top
    | r4_tsep_1(X0_56,X1_56,X2_56) != iProver_top
    | v1_funct_2(X0_57,u1_struct_0(X0_56),u1_struct_0(X3_56)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X3_56)))) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | v2_pre_topc(X3_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | l1_pre_topc(X3_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X3_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1122])).

cnf(c_9851,plain,
    ( sP1(sK8,sK7,X0_57,sK9,X0_56) = iProver_top
    | r4_tsep_1(sK7,sK8,sK9) != iProver_top
    | v1_funct_2(X0_57,u1_struct_0(sK7),u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0_56)))) != iProver_top
    | m1_pre_topc(sK8,sK7) != iProver_top
    | m1_pre_topc(sK9,sK7) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_2464])).

cnf(c_81,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_82,plain,
    ( v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_81])).

cnf(c_80,negated_conjecture,
    ( v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_83,plain,
    ( v2_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_80])).

cnf(c_79,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_84,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_79])).

cnf(c_78,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_85,plain,
    ( v2_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_78])).

cnf(c_77,negated_conjecture,
    ( m1_pre_topc(sK8,sK7) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_86,plain,
    ( m1_pre_topc(sK8,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_77])).

cnf(c_76,negated_conjecture,
    ( ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_87,plain,
    ( v2_struct_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_76])).

cnf(c_75,negated_conjecture,
    ( m1_pre_topc(sK9,sK7) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_88,plain,
    ( m1_pre_topc(sK9,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_75])).

cnf(c_71,negated_conjecture,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_93,plain,
    ( r3_tsep_1(sK7,sK8,sK9) != iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top
    | v2_struct_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_70,negated_conjecture,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | v2_pre_topc(sK10) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_94,plain,
    ( r3_tsep_1(sK7,sK8,sK9) != iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top
    | v2_pre_topc(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_70])).

cnf(c_69,negated_conjecture,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | l1_pre_topc(sK10) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_95,plain,
    ( r3_tsep_1(sK7,sK8,sK9) != iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top
    | l1_pre_topc(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_68,negated_conjecture,
    ( ~ sP3(sK10,sK7,sK9,sK8)
    | ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_96,plain,
    ( sP3(sK10,sK7,sK9,sK8) != iProver_top
    | r3_tsep_1(sK7,sK8,sK9) != iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_68])).

cnf(c_63,plain,
    ( sP3(X0,X1,X2,X3)
    | v1_funct_1(sK6(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1087,plain,
    ( sP3(X0_56,X1_56,X2_56,X3_56)
    | v1_funct_1(sK6(X0_56,X1_56,X2_56,X3_56)) ),
    inference(subtyping,[status(esa)],[c_63])).

cnf(c_3963,plain,
    ( sP3(sK10,sK7,sK9,sK8)
    | v1_funct_1(sK6(sK10,sK7,sK9,sK8)) ),
    inference(instantiation,[status(thm)],[c_1087])).

cnf(c_3964,plain,
    ( sP3(sK10,sK7,sK9,sK8) = iProver_top
    | v1_funct_1(sK6(sK10,sK7,sK9,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3963])).

cnf(c_62,plain,
    ( sP3(X0,X1,X2,X3)
    | v1_funct_2(sK6(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_1088,plain,
    ( sP3(X0_56,X1_56,X2_56,X3_56)
    | v1_funct_2(sK6(X0_56,X1_56,X2_56,X3_56),u1_struct_0(X1_56),u1_struct_0(X0_56)) ),
    inference(subtyping,[status(esa)],[c_62])).

cnf(c_3962,plain,
    ( sP3(sK10,sK7,sK9,sK8)
    | v1_funct_2(sK6(sK10,sK7,sK9,sK8),u1_struct_0(sK7),u1_struct_0(sK10)) ),
    inference(instantiation,[status(thm)],[c_1088])).

cnf(c_3966,plain,
    ( sP3(sK10,sK7,sK9,sK8) = iProver_top
    | v1_funct_2(sK6(sK10,sK7,sK9,sK8),u1_struct_0(sK7),u1_struct_0(sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3962])).

cnf(c_61,plain,
    ( sP3(X0,X1,X2,X3)
    | m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_1089,plain,
    ( sP3(X0_56,X1_56,X2_56,X3_56)
    | m1_subset_1(sK6(X0_56,X1_56,X2_56,X3_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(X0_56)))) ),
    inference(subtyping,[status(esa)],[c_61])).

cnf(c_3961,plain,
    ( sP3(sK10,sK7,sK9,sK8)
    | m1_subset_1(sK6(sK10,sK7,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK10)))) ),
    inference(instantiation,[status(thm)],[c_1089])).

cnf(c_3968,plain,
    ( sP3(sK10,sK7,sK9,sK8) = iProver_top
    | m1_subset_1(sK6(sK10,sK7,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK10)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3961])).

cnf(c_60,plain,
    ( sP3(X0,X1,X2,X3)
    | v1_funct_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3)) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_1090,plain,
    ( sP3(X0_56,X1_56,X2_56,X3_56)
    | v1_funct_1(k2_tmap_1(X1_56,X0_56,sK6(X0_56,X1_56,X2_56,X3_56),X3_56)) ),
    inference(subtyping,[status(esa)],[c_60])).

cnf(c_3960,plain,
    ( sP3(sK10,sK7,sK9,sK8)
    | v1_funct_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8)) ),
    inference(instantiation,[status(thm)],[c_1090])).

cnf(c_3970,plain,
    ( sP3(sK10,sK7,sK9,sK8) = iProver_top
    | v1_funct_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3960])).

cnf(c_56,plain,
    ( sP3(X0,X1,X2,X3)
    | v1_funct_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2)) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_1094,plain,
    ( sP3(X0_56,X1_56,X2_56,X3_56)
    | v1_funct_1(k2_tmap_1(X1_56,X0_56,sK6(X0_56,X1_56,X2_56,X3_56),X2_56)) ),
    inference(subtyping,[status(esa)],[c_56])).

cnf(c_3959,plain,
    ( sP3(sK10,sK7,sK9,sK8)
    | v1_funct_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9)) ),
    inference(instantiation,[status(thm)],[c_1094])).

cnf(c_3972,plain,
    ( sP3(sK10,sK7,sK9,sK8) = iProver_top
    | v1_funct_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3959])).

cnf(c_59,plain,
    ( sP3(X0,X1,X2,X3)
    | v1_funct_2(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3),u1_struct_0(X3),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_1091,plain,
    ( sP3(X0_56,X1_56,X2_56,X3_56)
    | v1_funct_2(k2_tmap_1(X1_56,X0_56,sK6(X0_56,X1_56,X2_56,X3_56),X3_56),u1_struct_0(X3_56),u1_struct_0(X0_56)) ),
    inference(subtyping,[status(esa)],[c_59])).

cnf(c_3958,plain,
    ( sP3(sK10,sK7,sK9,sK8)
    | v1_funct_2(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8),u1_struct_0(sK8),u1_struct_0(sK10)) ),
    inference(instantiation,[status(thm)],[c_1091])).

cnf(c_3974,plain,
    ( sP3(sK10,sK7,sK9,sK8) = iProver_top
    | v1_funct_2(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8),u1_struct_0(sK8),u1_struct_0(sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3958])).

cnf(c_58,plain,
    ( sP3(X0,X1,X2,X3)
    | v5_pre_topc(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3),X3,X0) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_1092,plain,
    ( sP3(X0_56,X1_56,X2_56,X3_56)
    | v5_pre_topc(k2_tmap_1(X1_56,X0_56,sK6(X0_56,X1_56,X2_56,X3_56),X3_56),X3_56,X0_56) ),
    inference(subtyping,[status(esa)],[c_58])).

cnf(c_3957,plain,
    ( sP3(sK10,sK7,sK9,sK8)
    | v5_pre_topc(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8),sK8,sK10) ),
    inference(instantiation,[status(thm)],[c_1092])).

cnf(c_3976,plain,
    ( sP3(sK10,sK7,sK9,sK8) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8),sK8,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3957])).

cnf(c_57,plain,
    ( sP3(X0,X1,X2,X3)
    | m1_subset_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_1093,plain,
    ( sP3(X0_56,X1_56,X2_56,X3_56)
    | m1_subset_1(k2_tmap_1(X1_56,X0_56,sK6(X0_56,X1_56,X2_56,X3_56),X3_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_56),u1_struct_0(X0_56)))) ),
    inference(subtyping,[status(esa)],[c_57])).

cnf(c_3956,plain,
    ( sP3(sK10,sK7,sK9,sK8)
    | m1_subset_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK10)))) ),
    inference(instantiation,[status(thm)],[c_1093])).

cnf(c_3978,plain,
    ( sP3(sK10,sK7,sK9,sK8) = iProver_top
    | m1_subset_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK10)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3956])).

cnf(c_55,plain,
    ( sP3(X0,X1,X2,X3)
    | v1_funct_2(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_1095,plain,
    ( sP3(X0_56,X1_56,X2_56,X3_56)
    | v1_funct_2(k2_tmap_1(X1_56,X0_56,sK6(X0_56,X1_56,X2_56,X3_56),X2_56),u1_struct_0(X2_56),u1_struct_0(X0_56)) ),
    inference(subtyping,[status(esa)],[c_55])).

cnf(c_3955,plain,
    ( sP3(sK10,sK7,sK9,sK8)
    | v1_funct_2(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),u1_struct_0(sK9),u1_struct_0(sK10)) ),
    inference(instantiation,[status(thm)],[c_1095])).

cnf(c_3980,plain,
    ( sP3(sK10,sK7,sK9,sK8) = iProver_top
    | v1_funct_2(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),u1_struct_0(sK9),u1_struct_0(sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3955])).

cnf(c_54,plain,
    ( sP3(X0,X1,X2,X3)
    | v5_pre_topc(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2),X2,X0) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_1096,plain,
    ( sP3(X0_56,X1_56,X2_56,X3_56)
    | v5_pre_topc(k2_tmap_1(X1_56,X0_56,sK6(X0_56,X1_56,X2_56,X3_56),X2_56),X2_56,X0_56) ),
    inference(subtyping,[status(esa)],[c_54])).

cnf(c_3954,plain,
    ( sP3(sK10,sK7,sK9,sK8)
    | v5_pre_topc(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),sK9,sK10) ),
    inference(instantiation,[status(thm)],[c_1096])).

cnf(c_3982,plain,
    ( sP3(sK10,sK7,sK9,sK8) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),sK9,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3954])).

cnf(c_53,plain,
    ( sP3(X0,X1,X2,X3)
    | m1_subset_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_1097,plain,
    ( sP3(X0_56,X1_56,X2_56,X3_56)
    | m1_subset_1(k2_tmap_1(X1_56,X0_56,sK6(X0_56,X1_56,X2_56,X3_56),X2_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X0_56)))) ),
    inference(subtyping,[status(esa)],[c_53])).

cnf(c_3953,plain,
    ( sP3(sK10,sK7,sK9,sK8)
    | m1_subset_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK10)))) ),
    inference(instantiation,[status(thm)],[c_1097])).

cnf(c_3984,plain,
    ( sP3(sK10,sK7,sK9,sK8) = iProver_top
    | m1_subset_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK10)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3953])).

cnf(c_10,plain,
    ( ~ r4_tsep_1(X0,X1,X2)
    | r4_tsep_1(X0,X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1137,plain,
    ( ~ r4_tsep_1(X0_56,X1_56,X2_56)
    | r4_tsep_1(X0_56,X2_56,X1_56)
    | ~ m1_pre_topc(X2_56,X0_56)
    | ~ m1_pre_topc(X1_56,X0_56)
    | ~ l1_pre_topc(X0_56) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3991,plain,
    ( ~ r4_tsep_1(sK7,sK8,sK9)
    | r4_tsep_1(sK7,sK9,sK8)
    | ~ m1_pre_topc(sK8,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_1137])).

cnf(c_3992,plain,
    ( r4_tsep_1(sK7,sK8,sK9) != iProver_top
    | r4_tsep_1(sK7,sK9,sK8) = iProver_top
    | m1_pre_topc(sK8,sK7) != iProver_top
    | m1_pre_topc(sK9,sK7) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3991])).

cnf(c_16,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1131,plain,
    ( sP0(X0_56,X1_56,X0_57,X2_56,X3_56)
    | ~ v5_pre_topc(k2_tmap_1(X2_56,X0_56,X0_57,X1_56),X1_56,X0_56)
    | ~ v5_pre_topc(k2_tmap_1(X2_56,X0_56,X0_57,X3_56),X3_56,X0_56)
    | ~ v1_funct_2(k2_tmap_1(X2_56,X0_56,X0_57,X1_56),u1_struct_0(X1_56),u1_struct_0(X0_56))
    | ~ v1_funct_2(k2_tmap_1(X2_56,X0_56,X0_57,X3_56),u1_struct_0(X3_56),u1_struct_0(X0_56))
    | ~ m1_subset_1(k2_tmap_1(X2_56,X0_56,X0_57,X1_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(X0_56))))
    | ~ m1_subset_1(k2_tmap_1(X2_56,X0_56,X0_57,X3_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_56),u1_struct_0(X0_56))))
    | ~ v1_funct_1(k2_tmap_1(X2_56,X0_56,X0_57,X1_56))
    | ~ v1_funct_1(k2_tmap_1(X2_56,X0_56,X0_57,X3_56)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_4111,plain,
    ( sP0(sK10,X0_56,sK6(sK10,sK7,sK9,sK8),sK7,sK9)
    | ~ v5_pre_topc(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),X0_56),X0_56,sK10)
    | ~ v5_pre_topc(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),sK9,sK10)
    | ~ v1_funct_2(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),X0_56),u1_struct_0(X0_56),u1_struct_0(sK10))
    | ~ v1_funct_2(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),u1_struct_0(sK9),u1_struct_0(sK10))
    | ~ m1_subset_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK10))))
    | ~ m1_subset_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK10))))
    | ~ v1_funct_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),X0_56))
    | ~ v1_funct_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9)) ),
    inference(instantiation,[status(thm)],[c_1131])).

cnf(c_4112,plain,
    ( sP0(sK10,X0_56,sK6(sK10,sK7,sK9,sK8),sK7,sK9) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),X0_56),X0_56,sK10) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),sK9,sK10) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),X0_56),u1_struct_0(X0_56),u1_struct_0(sK10)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),u1_struct_0(sK9),u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK10)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK10)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),X0_56)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4111])).

cnf(c_4114,plain,
    ( sP0(sK10,sK8,sK6(sK10,sK7,sK9,sK8),sK7,sK9) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8),sK8,sK10) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),sK9,sK10) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8),u1_struct_0(sK8),u1_struct_0(sK10)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),u1_struct_0(sK9),u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK10)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK10)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4112])).

cnf(c_1076,negated_conjecture,
    ( m1_pre_topc(sK8,sK7) ),
    inference(subtyping,[status(esa)],[c_77])).

cnf(c_2509,plain,
    ( m1_pre_topc(sK8,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1076])).

cnf(c_1078,negated_conjecture,
    ( m1_pre_topc(sK9,sK7) ),
    inference(subtyping,[status(esa)],[c_75])).

cnf(c_2507,plain,
    ( m1_pre_topc(sK9,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1078])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | k1_tsep_1(X1,X0,X2) = k1_tsep_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1147,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_pre_topc(X2_56,X1_56)
    | ~ l1_pre_topc(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X2_56)
    | k1_tsep_1(X1_56,X0_56,X2_56) = k1_tsep_1(X1_56,X2_56,X0_56) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2439,plain,
    ( k1_tsep_1(X0_56,X1_56,X2_56) = k1_tsep_1(X0_56,X2_56,X1_56)
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1147])).

cnf(c_3562,plain,
    ( k1_tsep_1(sK7,sK9,X0_56) = k1_tsep_1(sK7,X0_56,sK9)
    | m1_pre_topc(X0_56,sK7) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2507,c_2439])).

cnf(c_4392,plain,
    ( m1_pre_topc(X0_56,sK7) != iProver_top
    | k1_tsep_1(sK7,sK9,X0_56) = k1_tsep_1(sK7,X0_56,sK9)
    | v2_struct_0(X0_56) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3562,c_82,c_84,c_87])).

cnf(c_4393,plain,
    ( k1_tsep_1(sK7,sK9,X0_56) = k1_tsep_1(sK7,X0_56,sK9)
    | m1_pre_topc(X0_56,sK7) != iProver_top
    | v2_struct_0(X0_56) = iProver_top ),
    inference(renaming,[status(thm)],[c_4392])).

cnf(c_4402,plain,
    ( k1_tsep_1(sK7,sK9,sK8) = k1_tsep_1(sK7,sK8,sK9)
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2509,c_4393])).

cnf(c_4423,plain,
    ( k1_tsep_1(sK7,sK9,sK8) = sK7
    | v2_struct_0(sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4402,c_1079])).

cnf(c_51,plain,
    ( r3_tsep_1(X0,X1,X2)
    | ~ r4_tsep_1(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1098,plain,
    ( r3_tsep_1(X0_56,X1_56,X2_56)
    | ~ r4_tsep_1(X0_56,X1_56,X2_56)
    | ~ r1_tsep_1(X1_56,X2_56)
    | ~ m1_pre_topc(X2_56,X0_56)
    | ~ m1_pre_topc(X1_56,X0_56)
    | ~ v2_pre_topc(X0_56)
    | ~ l1_pre_topc(X0_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X2_56) ),
    inference(subtyping,[status(esa)],[c_51])).

cnf(c_3903,plain,
    ( r3_tsep_1(X0_56,sK8,sK9)
    | ~ r4_tsep_1(X0_56,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ m1_pre_topc(sK8,X0_56)
    | ~ m1_pre_topc(sK9,X0_56)
    | ~ v2_pre_topc(X0_56)
    | ~ l1_pre_topc(X0_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1098])).

cnf(c_5062,plain,
    ( r3_tsep_1(sK7,sK8,sK9)
    | ~ r4_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ m1_pre_topc(sK8,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3903])).

cnf(c_5063,plain,
    ( r3_tsep_1(sK7,sK8,sK9) = iProver_top
    | r4_tsep_1(sK7,sK8,sK9) != iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top
    | m1_pre_topc(sK8,sK7) != iProver_top
    | m1_pre_topc(sK9,sK7) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5062])).

cnf(c_12,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(X2,X1,X4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1135,plain,
    ( ~ sP1(X0_56,X1_56,X0_57,X2_56,X3_56)
    | ~ sP0(X3_56,X2_56,X0_57,X1_56,X0_56)
    | v5_pre_topc(X0_57,X1_56,X3_56) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_5205,plain,
    ( ~ sP1(sK9,sK7,sK6(sK10,sK7,sK9,sK8),X0_56,sK10)
    | ~ sP0(sK10,X0_56,sK6(sK10,sK7,sK9,sK8),sK7,sK9)
    | v5_pre_topc(sK6(sK10,sK7,sK9,sK8),sK7,sK10) ),
    inference(instantiation,[status(thm)],[c_1135])).

cnf(c_5216,plain,
    ( sP1(sK9,sK7,sK6(sK10,sK7,sK9,sK8),X0_56,sK10) != iProver_top
    | sP0(sK10,X0_56,sK6(sK10,sK7,sK9,sK8),sK7,sK9) != iProver_top
    | v5_pre_topc(sK6(sK10,sK7,sK9,sK8),sK7,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5205])).

cnf(c_5218,plain,
    ( sP1(sK9,sK7,sK6(sK10,sK7,sK9,sK8),sK8,sK10) != iProver_top
    | sP0(sK10,sK8,sK6(sK10,sK7,sK9,sK8),sK7,sK9) != iProver_top
    | v5_pre_topc(sK6(sK10,sK7,sK9,sK8),sK7,sK10) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5216])).

cnf(c_1169,plain,
    ( ~ r3_tsep_1(X0_56,X1_56,X2_56)
    | r3_tsep_1(X3_56,X4_56,X5_56)
    | X3_56 != X0_56
    | X4_56 != X1_56
    | X5_56 != X2_56 ),
    theory(equality)).

cnf(c_1154,plain,
    ( X0_56 != X1_56
    | X2_56 != X1_56
    | X2_56 = X0_56 ),
    theory(equality)).

cnf(c_3861,plain,
    ( X0_56 != sK7
    | k1_tsep_1(sK7,sK8,sK9) = X0_56 ),
    inference(resolution,[status(thm)],[c_1154,c_1079])).

cnf(c_4945,plain,
    ( ~ r3_tsep_1(X0_56,X1_56,X2_56)
    | r3_tsep_1(X3_56,X4_56,k1_tsep_1(sK7,sK8,sK9))
    | X3_56 != X0_56
    | X4_56 != X1_56
    | X2_56 != sK7 ),
    inference(resolution,[status(thm)],[c_1169,c_3861])).

cnf(c_5475,plain,
    ( ~ r3_tsep_1(X0_56,X1_56,X2_56)
    | r3_tsep_1(X3_56,k1_tsep_1(sK7,sK8,sK9),k1_tsep_1(sK7,sK8,sK9))
    | X3_56 != X0_56
    | X1_56 != sK7
    | X2_56 != sK7 ),
    inference(resolution,[status(thm)],[c_4945,c_3861])).

cnf(c_5572,plain,
    ( r3_tsep_1(k1_tsep_1(sK7,sK8,sK9),k1_tsep_1(sK7,sK8,sK9),k1_tsep_1(sK7,sK8,sK9))
    | ~ r3_tsep_1(sK7,X0_56,X1_56)
    | X0_56 != sK7
    | X1_56 != sK7 ),
    inference(resolution,[status(thm)],[c_5475,c_1079])).

cnf(c_73,negated_conjecture,
    ( r3_tsep_1(sK7,sK8,sK9)
    | r1_tsep_1(sK8,sK9) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_1080,negated_conjecture,
    ( r3_tsep_1(sK7,sK8,sK9)
    | r1_tsep_1(sK8,sK9) ),
    inference(subtyping,[status(esa)],[c_73])).

cnf(c_5606,plain,
    ( r3_tsep_1(k1_tsep_1(sK7,sK8,sK9),k1_tsep_1(sK7,sK8,sK9),k1_tsep_1(sK7,sK8,sK9))
    | r1_tsep_1(sK8,sK9)
    | sK8 != sK7
    | sK9 != sK7 ),
    inference(resolution,[status(thm)],[c_5572,c_1080])).

cnf(c_50,plain,
    ( ~ r3_tsep_1(X0,X1,X2)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1100,plain,
    ( ~ r3_tsep_1(X0_56,X1_56,X2_56)
    | r1_tsep_1(X1_56,X2_56)
    | ~ m1_pre_topc(X2_56,X0_56)
    | ~ m1_pre_topc(X1_56,X0_56)
    | ~ v2_pre_topc(X0_56)
    | ~ l1_pre_topc(X0_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X2_56) ),
    inference(subtyping,[status(esa)],[c_50])).

cnf(c_3605,plain,
    ( ~ r3_tsep_1(sK7,X0_56,X1_56)
    | r1_tsep_1(X0_56,X1_56)
    | ~ m1_pre_topc(X0_56,sK7)
    | ~ m1_pre_topc(X1_56,sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1100])).

cnf(c_3837,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | r1_tsep_1(sK8,sK9)
    | ~ m1_pre_topc(sK8,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3605])).

cnf(c_5647,plain,
    ( r1_tsep_1(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5606,c_81,c_80,c_79,c_78,c_77,c_76,c_75,c_73,c_3837])).

cnf(c_5649,plain,
    ( r1_tsep_1(sK8,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5647])).

cnf(c_4566,plain,
    ( sP1(X0_56,sK7,sK6(sK10,sK7,sK9,sK8),X1_56,sK10)
    | ~ r4_tsep_1(sK7,X0_56,X1_56)
    | ~ v1_funct_2(sK6(sK10,sK7,sK9,sK8),u1_struct_0(sK7),u1_struct_0(sK10))
    | ~ m1_subset_1(sK6(sK10,sK7,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK10))))
    | ~ m1_pre_topc(X0_56,sK7)
    | ~ m1_pre_topc(X1_56,sK7)
    | ~ v2_pre_topc(sK7)
    | ~ v2_pre_topc(sK10)
    | ~ v1_funct_1(sK6(sK10,sK7,sK9,sK8))
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK10)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(sK7)
    | v2_struct_0(sK10)
    | k1_tsep_1(sK7,X0_56,X1_56) != sK7 ),
    inference(instantiation,[status(thm)],[c_1122])).

cnf(c_6983,plain,
    ( sP1(sK9,sK7,sK6(sK10,sK7,sK9,sK8),sK8,sK10)
    | ~ r4_tsep_1(sK7,sK9,sK8)
    | ~ v1_funct_2(sK6(sK10,sK7,sK9,sK8),u1_struct_0(sK7),u1_struct_0(sK10))
    | ~ m1_subset_1(sK6(sK10,sK7,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK10))))
    | ~ m1_pre_topc(sK8,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | ~ v2_pre_topc(sK7)
    | ~ v2_pre_topc(sK10)
    | ~ v1_funct_1(sK6(sK10,sK7,sK9,sK8))
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK10)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v2_struct_0(sK7)
    | v2_struct_0(sK10)
    | k1_tsep_1(sK7,sK9,sK8) != sK7 ),
    inference(instantiation,[status(thm)],[c_4566])).

cnf(c_6984,plain,
    ( k1_tsep_1(sK7,sK9,sK8) != sK7
    | sP1(sK9,sK7,sK6(sK10,sK7,sK9,sK8),sK8,sK10) = iProver_top
    | r4_tsep_1(sK7,sK9,sK8) != iProver_top
    | v1_funct_2(sK6(sK10,sK7,sK9,sK8),u1_struct_0(sK7),u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(sK6(sK10,sK7,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK10)))) != iProver_top
    | m1_pre_topc(sK8,sK7) != iProver_top
    | m1_pre_topc(sK9,sK7) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK10) != iProver_top
    | v1_funct_1(sK6(sK10,sK7,sK9,sK8)) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK10) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6983])).

cnf(c_52,plain,
    ( sP3(X0,X1,X2,X3)
    | ~ v5_pre_topc(sK6(X0,X1,X2,X3),X1,X0)
    | ~ v1_funct_2(sK6(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ v1_funct_1(sK6(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_664,plain,
    ( ~ v5_pre_topc(sK6(X0,X1,X2,X3),X1,X0)
    | sP3(X0,X1,X2,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_52,c_63,c_62,c_61])).

cnf(c_665,plain,
    ( sP3(X0,X1,X2,X3)
    | ~ v5_pre_topc(sK6(X0,X1,X2,X3),X1,X0) ),
    inference(renaming,[status(thm)],[c_664])).

cnf(c_1071,plain,
    ( sP3(X0_56,X1_56,X2_56,X3_56)
    | ~ v5_pre_topc(sK6(X0_56,X1_56,X2_56,X3_56),X1_56,X0_56) ),
    inference(subtyping,[status(esa)],[c_665])).

cnf(c_7641,plain,
    ( sP3(sK10,sK7,sK9,sK8)
    | ~ v5_pre_topc(sK6(sK10,sK7,sK9,sK8),sK7,sK10) ),
    inference(instantiation,[status(thm)],[c_1071])).

cnf(c_7642,plain,
    ( sP3(sK10,sK7,sK9,sK8) = iProver_top
    | v5_pre_topc(sK6(sK10,sK7,sK9,sK8),sK7,sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7641])).

cnf(c_11372,plain,
    ( r4_tsep_1(sK7,sK8,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9851,c_82,c_83,c_84,c_85,c_86,c_87,c_88,c_93,c_94,c_95,c_96,c_3964,c_3966,c_3968,c_3970,c_3972,c_3974,c_3976,c_3978,c_3980,c_3982,c_3984,c_3992,c_4114,c_4423,c_5063,c_5218,c_5649,c_6984,c_7642])).

cnf(c_11374,plain,
    ( ~ r4_tsep_1(sK7,sK8,sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11372])).

cnf(c_45,plain,
    ( r3_tsep_1(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_struct_0(sK5(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1102,plain,
    ( r3_tsep_1(X0_56,X1_56,X2_56)
    | ~ r1_tsep_1(X1_56,X2_56)
    | ~ m1_pre_topc(X2_56,X0_56)
    | ~ m1_pre_topc(X1_56,X0_56)
    | ~ v2_pre_topc(X0_56)
    | ~ l1_pre_topc(X0_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X2_56)
    | ~ v2_struct_0(sK5(X0_56,X1_56,X2_56)) ),
    inference(subtyping,[status(esa)],[c_45])).

cnf(c_10858,plain,
    ( r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ m1_pre_topc(sK8,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7)
    | ~ v2_struct_0(sK5(sK7,sK8,sK9))
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1102])).

cnf(c_27,plain,
    ( sP2(X0,X1,X2,X3)
    | m1_subset_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1120,plain,
    ( sP2(X0_56,X1_56,X2_56,X3_56)
    | m1_subset_1(k2_tmap_1(X3_56,X0_56,sK4(X0_56,X1_56,X2_56,X3_56),X1_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(X0_56)))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_6105,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7)
    | m1_subset_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK7,sK8,sK9))))) ),
    inference(instantiation,[status(thm)],[c_1120])).

cnf(c_28,plain,
    ( sP2(X0,X1,X2,X3)
    | v5_pre_topc(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1),X1,X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1119,plain,
    ( sP2(X0_56,X1_56,X2_56,X3_56)
    | v5_pre_topc(k2_tmap_1(X3_56,X0_56,sK4(X0_56,X1_56,X2_56,X3_56),X1_56),X1_56,X0_56) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_6106,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7)
    | v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK9),sK9,sK5(sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_1119])).

cnf(c_29,plain,
    ( sP2(X0,X1,X2,X3)
    | v1_funct_2(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1),u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1118,plain,
    ( sP2(X0_56,X1_56,X2_56,X3_56)
    | v1_funct_2(k2_tmap_1(X3_56,X0_56,sK4(X0_56,X1_56,X2_56,X3_56),X1_56),u1_struct_0(X1_56),u1_struct_0(X0_56)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_6107,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7)
    | v1_funct_2(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK9),u1_struct_0(sK9),u1_struct_0(sK5(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_1118])).

cnf(c_31,plain,
    ( sP2(X0,X1,X2,X3)
    | m1_subset_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1116,plain,
    ( sP2(X0_56,X1_56,X2_56,X3_56)
    | m1_subset_1(k2_tmap_1(X3_56,X0_56,sK4(X0_56,X1_56,X2_56,X3_56),X2_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X0_56)))) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_6108,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7)
    | m1_subset_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK5(sK7,sK8,sK9))))) ),
    inference(instantiation,[status(thm)],[c_1116])).

cnf(c_32,plain,
    ( sP2(X0,X1,X2,X3)
    | v5_pre_topc(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2),X2,X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1115,plain,
    ( sP2(X0_56,X1_56,X2_56,X3_56)
    | v5_pre_topc(k2_tmap_1(X3_56,X0_56,sK4(X0_56,X1_56,X2_56,X3_56),X2_56),X2_56,X0_56) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_6109,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7)
    | v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8),sK8,sK5(sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_1115])).

cnf(c_33,plain,
    ( sP2(X0,X1,X2,X3)
    | v1_funct_2(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1114,plain,
    ( sP2(X0_56,X1_56,X2_56,X3_56)
    | v1_funct_2(k2_tmap_1(X3_56,X0_56,sK4(X0_56,X1_56,X2_56,X3_56),X2_56),u1_struct_0(X2_56),u1_struct_0(X0_56)) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_6110,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7)
    | v1_funct_2(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8),u1_struct_0(sK8),u1_struct_0(sK5(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_1114])).

cnf(c_30,plain,
    ( sP2(X0,X1,X2,X3)
    | v1_funct_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1117,plain,
    ( sP2(X0_56,X1_56,X2_56,X3_56)
    | v1_funct_1(k2_tmap_1(X3_56,X0_56,sK4(X0_56,X1_56,X2_56,X3_56),X1_56)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_6111,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7)
    | v1_funct_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK9)) ),
    inference(instantiation,[status(thm)],[c_1117])).

cnf(c_34,plain,
    ( sP2(X0,X1,X2,X3)
    | v1_funct_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1113,plain,
    ( sP2(X0_56,X1_56,X2_56,X3_56)
    | v1_funct_1(k2_tmap_1(X3_56,X0_56,sK4(X0_56,X1_56,X2_56,X3_56),X2_56)) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_6112,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7)
    | v1_funct_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8)) ),
    inference(instantiation,[status(thm)],[c_1113])).

cnf(c_35,plain,
    ( sP2(X0,X1,X2,X3)
    | m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1112,plain,
    ( sP2(X0_56,X1_56,X2_56,X3_56)
    | m1_subset_1(sK4(X0_56,X1_56,X2_56,X3_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_56),u1_struct_0(X0_56)))) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_6113,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7)
    | m1_subset_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))))) ),
    inference(instantiation,[status(thm)],[c_1112])).

cnf(c_36,plain,
    ( sP2(X0,X1,X2,X3)
    | v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1111,plain,
    ( sP2(X0_56,X1_56,X2_56,X3_56)
    | v1_funct_2(sK4(X0_56,X1_56,X2_56,X3_56),u1_struct_0(X3_56),u1_struct_0(X0_56)) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_6114,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7)
    | v1_funct_2(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_1111])).

cnf(c_37,plain,
    ( sP2(X0,X1,X2,X3)
    | v1_funct_1(sK4(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1110,plain,
    ( sP2(X0_56,X1_56,X2_56,X3_56)
    | v1_funct_1(sK4(X0_56,X1_56,X2_56,X3_56)) ),
    inference(subtyping,[status(esa)],[c_37])).

cnf(c_6116,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7)
    | v1_funct_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_1110])).

cnf(c_72,negated_conjecture,
    ( sP3(X0,sK7,sK9,sK8)
    | r3_tsep_1(sK7,sK8,sK9)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_1081,negated_conjecture,
    ( sP3(X0_56,sK7,sK9,sK8)
    | r3_tsep_1(sK7,sK8,sK9)
    | ~ v2_pre_topc(X0_56)
    | ~ l1_pre_topc(X0_56)
    | v2_struct_0(X0_56) ),
    inference(subtyping,[status(esa)],[c_72])).

cnf(c_6071,plain,
    ( sP3(sK5(sK7,sK8,sK9),sK7,sK9,sK8)
    | r3_tsep_1(sK7,sK8,sK9)
    | ~ v2_pre_topc(sK5(sK7,sK8,sK9))
    | ~ l1_pre_topc(sK5(sK7,sK8,sK9))
    | v2_struct_0(sK5(sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_1081])).

cnf(c_6,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1141,plain,
    ( l1_struct_0(X0_56)
    | ~ l1_pre_topc(X0_56) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_6075,plain,
    ( l1_struct_0(sK5(sK7,sK8,sK9))
    | ~ l1_pre_topc(sK5(sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_1141])).

cnf(c_42,plain,
    ( ~ sP2(sK5(X0,X1,X2),X2,X1,X0)
    | r3_tsep_1(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1105,plain,
    ( ~ sP2(sK5(X0_56,X1_56,X2_56),X2_56,X1_56,X0_56)
    | r3_tsep_1(X0_56,X1_56,X2_56)
    | ~ r1_tsep_1(X1_56,X2_56)
    | ~ m1_pre_topc(X2_56,X0_56)
    | ~ m1_pre_topc(X1_56,X0_56)
    | ~ v2_pre_topc(X0_56)
    | ~ l1_pre_topc(X0_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X2_56) ),
    inference(subtyping,[status(esa)],[c_42])).

cnf(c_3900,plain,
    ( ~ sP2(sK5(X0_56,sK8,sK9),sK9,sK8,X0_56)
    | r3_tsep_1(X0_56,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ m1_pre_topc(sK8,X0_56)
    | ~ m1_pre_topc(sK9,X0_56)
    | ~ v2_pre_topc(X0_56)
    | ~ l1_pre_topc(X0_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1105])).

cnf(c_5158,plain,
    ( ~ sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7)
    | r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ m1_pre_topc(sK8,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3900])).

cnf(c_1149,plain,
    ( X0_56 = X0_56 ),
    theory(equality)).

cnf(c_3863,plain,
    ( X0_56 != X1_56
    | X1_56 = X0_56 ),
    inference(resolution,[status(thm)],[c_1154,c_1149])).

cnf(c_4689,plain,
    ( sK7 = k1_tsep_1(sK7,sK8,sK9) ),
    inference(resolution,[status(thm)],[c_3863,c_1079])).

cnf(c_1156,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | m1_pre_topc(X2_56,X3_56)
    | X2_56 != X0_56
    | X3_56 != X1_56 ),
    theory(equality)).

cnf(c_4700,plain,
    ( ~ m1_pre_topc(X0_56,k1_tsep_1(sK7,sK8,sK9))
    | m1_pre_topc(X1_56,sK7)
    | X1_56 != X0_56 ),
    inference(resolution,[status(thm)],[c_4689,c_1156])).

cnf(c_4021,plain,
    ( m1_pre_topc(X0_56,k1_tsep_1(sK7,sK8,sK9))
    | ~ m1_pre_topc(X1_56,sK7)
    | X0_56 != X1_56 ),
    inference(resolution,[status(thm)],[c_1156,c_1079])).

cnf(c_4234,plain,
    ( m1_pre_topc(k1_tsep_1(sK7,sK8,sK9),k1_tsep_1(sK7,sK8,sK9))
    | ~ m1_pre_topc(sK7,sK7) ),
    inference(resolution,[status(thm)],[c_4021,c_1079])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1146,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_pre_topc(X2_56,X1_56)
    | m1_pre_topc(k1_tsep_1(X1_56,X2_56,X0_56),X1_56)
    | ~ l1_pre_topc(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X2_56) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2440,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | m1_pre_topc(X2_56,X1_56) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1_56,X2_56,X0_56),X1_56) = iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1146])).

cnf(c_3744,plain,
    ( m1_pre_topc(sK8,sK7) != iProver_top
    | m1_pre_topc(sK9,sK7) != iProver_top
    | m1_pre_topc(sK7,sK7) = iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_2440])).

cnf(c_3780,plain,
    ( ~ m1_pre_topc(sK8,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | m1_pre_topc(sK7,sK7)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v2_struct_0(sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3744])).

cnf(c_4365,plain,
    ( m1_pre_topc(k1_tsep_1(sK7,sK8,sK9),k1_tsep_1(sK7,sK8,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4234,c_81,c_79,c_78,c_77,c_76,c_75,c_3780])).

cnf(c_5136,plain,
    ( m1_pre_topc(X0_56,sK7)
    | X0_56 != k1_tsep_1(sK7,sK8,sK9) ),
    inference(resolution,[status(thm)],[c_4700,c_4365])).

cnf(c_5144,plain,
    ( m1_pre_topc(k1_tsep_1(sK7,sK8,sK9),sK7) ),
    inference(resolution,[status(thm)],[c_5136,c_1149])).

cnf(c_44,plain,
    ( r3_tsep_1(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK5(X0,X1,X2))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1103,plain,
    ( r3_tsep_1(X0_56,X1_56,X2_56)
    | ~ r1_tsep_1(X1_56,X2_56)
    | ~ m1_pre_topc(X2_56,X0_56)
    | ~ m1_pre_topc(X1_56,X0_56)
    | ~ v2_pre_topc(X0_56)
    | v2_pre_topc(sK5(X0_56,X1_56,X2_56))
    | ~ l1_pre_topc(X0_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X2_56) ),
    inference(subtyping,[status(esa)],[c_44])).

cnf(c_3902,plain,
    ( r3_tsep_1(X0_56,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ m1_pre_topc(sK8,X0_56)
    | ~ m1_pre_topc(sK9,X0_56)
    | ~ v2_pre_topc(X0_56)
    | v2_pre_topc(sK5(X0_56,sK8,sK9))
    | ~ l1_pre_topc(X0_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1103])).

cnf(c_5053,plain,
    ( r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ m1_pre_topc(sK8,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | v2_pre_topc(sK5(sK7,sK8,sK9))
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3902])).

cnf(c_43,plain,
    ( r3_tsep_1(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK5(X0,X1,X2))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1104,plain,
    ( r3_tsep_1(X0_56,X1_56,X2_56)
    | ~ r1_tsep_1(X1_56,X2_56)
    | ~ m1_pre_topc(X2_56,X0_56)
    | ~ m1_pre_topc(X1_56,X0_56)
    | ~ v2_pre_topc(X0_56)
    | ~ l1_pre_topc(X0_56)
    | l1_pre_topc(sK5(X0_56,X1_56,X2_56))
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X2_56) ),
    inference(subtyping,[status(esa)],[c_43])).

cnf(c_3901,plain,
    ( r3_tsep_1(X0_56,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ m1_pre_topc(sK8,X0_56)
    | ~ m1_pre_topc(sK9,X0_56)
    | ~ v2_pre_topc(X0_56)
    | ~ l1_pre_topc(X0_56)
    | l1_pre_topc(sK5(X0_56,sK8,sK9))
    | v2_struct_0(X0_56)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1104])).

cnf(c_5044,plain,
    ( r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ m1_pre_topc(sK8,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | ~ v2_pre_topc(sK7)
    | l1_pre_topc(sK5(sK7,sK8,sK9))
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3901])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1145,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_pre_topc(X2_56,X1_56)
    | ~ l1_pre_topc(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X2_56)
    | ~ v2_struct_0(k1_tsep_1(X1_56,X2_56,X0_56)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_4714,plain,
    ( ~ m1_pre_topc(sK8,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | ~ l1_pre_topc(sK7)
    | ~ v2_struct_0(k1_tsep_1(sK7,sK8,sK9))
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1145])).

cnf(c_3875,plain,
    ( l1_struct_0(k1_tsep_1(sK7,sK8,sK9))
    | ~ l1_pre_topc(k1_tsep_1(sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_1141])).

cnf(c_49,plain,
    ( ~ r3_tsep_1(X0,X1,X2)
    | r4_tsep_1(X0,X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1099,plain,
    ( ~ r3_tsep_1(X0_56,X1_56,X2_56)
    | r4_tsep_1(X0_56,X1_56,X2_56)
    | ~ m1_pre_topc(X2_56,X0_56)
    | ~ m1_pre_topc(X1_56,X0_56)
    | ~ v2_pre_topc(X0_56)
    | ~ l1_pre_topc(X0_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X2_56) ),
    inference(subtyping,[status(esa)],[c_49])).

cnf(c_3610,plain,
    ( ~ r3_tsep_1(sK7,X0_56,X1_56)
    | r4_tsep_1(sK7,X0_56,X1_56)
    | ~ m1_pre_topc(X0_56,sK7)
    | ~ m1_pre_topc(X1_56,sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1099])).

cnf(c_3840,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | r4_tsep_1(sK7,sK8,sK9)
    | ~ m1_pre_topc(sK8,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3610])).

cnf(c_1158,plain,
    ( ~ l1_pre_topc(X0_56)
    | l1_pre_topc(X1_56)
    | X1_56 != X0_56 ),
    theory(equality)).

cnf(c_3656,plain,
    ( l1_pre_topc(k1_tsep_1(sK7,sK8,sK9))
    | ~ l1_pre_topc(sK7) ),
    inference(resolution,[status(thm)],[c_1158,c_1079])).

cnf(c_3446,plain,
    ( l1_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_1141])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_83638,c_49496,c_44211,c_30978,c_22062,c_19355,c_11374,c_10858,c_6105,c_6106,c_6107,c_6108,c_6109,c_6110,c_6111,c_6112,c_6113,c_6114,c_6116,c_6071,c_6075,c_5647,c_5158,c_5144,c_5053,c_5044,c_4714,c_3875,c_3840,c_3656,c_3446,c_75,c_76,c_77,c_78,c_79,c_80,c_81])).


%------------------------------------------------------------------------------
