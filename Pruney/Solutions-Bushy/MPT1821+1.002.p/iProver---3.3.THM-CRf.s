%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1821+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:33 EST 2020

% Result     : Theorem 11.57s
% Output     : CNFRefutation 11.57s
% Verified   : 
% Statistics : Number of formulae       :  428 (42845 expanded)
%              Number of clauses        :  296 (8451 expanded)
%              Number of leaves         :   23 (12929 expanded)
%              Depth                    :   33
%              Number of atoms          : 3073 (784403 expanded)
%              Number of equality atoms :  860 (39939 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   40 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,plain,(
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

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f52,plain,(
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

fof(f53,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | v1_funct_1(sK4(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f7,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f42,plain,(
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

fof(f43,plain,(
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
    inference(definition_folding,[],[f36,f42])).

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
    inference(nnf_transformation,[],[f43])).

fof(f66,plain,(
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
    inference(flattening,[],[f65])).

fof(f67,plain,(
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
    inference(rectify,[],[f66])).

fof(f71,plain,(
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

fof(f70,plain,(
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

fof(f69,plain,(
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

fof(f68,plain,
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

fof(f72,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f67,f71,f70,f69,f68])).

fof(f150,plain,(
    k1_tsep_1(sK7,sK8,sK9) = sK7 ),
    inference(cnf_transformation,[],[f72])).

fof(f103,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X5,k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
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
      | ~ v1_funct_1(X5)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f145,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f72])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f81,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f149,plain,(
    m1_pre_topc(sK9,sK7) ),
    inference(cnf_transformation,[],[f72])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f82,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f147,plain,(
    m1_pre_topc(sK8,sK7) ),
    inference(cnf_transformation,[],[f72])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f143,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f72])).

fof(f146,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f72])).

fof(f148,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f72])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f144,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f72])).

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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f41,plain,(
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
    inference(definition_folding,[],[f32,f40])).

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
    inference(nnf_transformation,[],[f41])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f57,plain,(
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

fof(f58,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f56,f57])).

fof(f123,plain,(
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
    inference(cnf_transformation,[],[f58])).

fof(f120,plain,(
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
    inference(cnf_transformation,[],[f58])).

fof(f121,plain,(
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
    inference(cnf_transformation,[],[f58])).

fof(f122,plain,(
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
    inference(cnf_transformation,[],[f58])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f62,plain,(
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
    inference(rectify,[],[f61])).

fof(f63,plain,(
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

fof(f64,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f62,f63])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | v1_funct_1(sK6(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f118,plain,(
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

fof(f151,plain,
    ( r1_tsep_1(sK8,sK9)
    | r3_tsep_1(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f72])).

fof(f156,plain,
    ( ~ sP3(sK10,sK7,sK9,sK8)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ r3_tsep_1(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f72])).

fof(f153,plain,
    ( ~ v2_struct_0(sK10)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ r3_tsep_1(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f72])).

fof(f154,plain,
    ( v2_pre_topc(sK10)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ r3_tsep_1(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f72])).

fof(f155,plain,
    ( l1_pre_topc(sK10)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ r3_tsep_1(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f72])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | ~ m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(sK6(X0,X1,X2,X3),X1,X0)
      | ~ v1_funct_2(sK6(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(sK6(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | v1_funct_2(sK6(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | v1_funct_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | v1_funct_2(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3),u1_struct_0(X3),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f136,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | v5_pre_topc(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3),X3,X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | m1_subset_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | v1_funct_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | v1_funct_2(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f140,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | v5_pre_topc(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2),X2,X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f141,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | m1_subset_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f37,plain,(
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

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f100,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f38,plain,(
    ! [X3,X0,X2,X4,X1] :
      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
      <=> sP0(X1,X4,X2,X0,X3) )
      | ~ sP1(X3,X0,X2,X4,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f39,plain,(
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
    inference(definition_folding,[],[f30,f38,f37])).

fof(f101,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f126,plain,(
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
    inference(cnf_transformation,[],[f60])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X1,X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | ~ m1_subset_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),k1_tsep_1(X3,X2,X1),X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f129,plain,(
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
    inference(cnf_transformation,[],[f64])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | v1_funct_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | v5_pre_topc(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1),X1,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | v1_funct_2(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | m1_subset_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | m1_subset_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | v5_pre_topc(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2),X2,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | v1_funct_2(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | v1_funct_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f152,plain,(
    ! [X4] :
      ( sP3(X4,sK7,sK9,sK8)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | r3_tsep_1(sK7,sK8,sK9) ) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_38,plain,
    ( sP2(X0,X1,X2,X3)
    | m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_14278,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58)
    | m1_subset_1(sK4(X0_58,X1_58,X2_58,X3_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X0_58)))) ),
    inference(subtyping,[status(esa)],[c_38])).

cnf(c_15761,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | m1_subset_1(sK4(X0_58,X1_58,X2_58,X3_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X0_58)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14278])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_14302,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
    | ~ v1_funct_1(X0_59)
    | k2_partfun1(X0_60,X1_60,X0_59,X2_60) = k7_relat_1(X0_59,X2_60) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_15737,plain,
    ( k2_partfun1(X0_60,X1_60,X0_59,X2_60) = k7_relat_1(X0_59,X2_60)
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14302])).

cnf(c_18338,plain,
    ( k2_partfun1(u1_struct_0(X0_58),u1_struct_0(X1_58),sK4(X1_58,X2_58,X3_58,X0_58),X0_60) = k7_relat_1(sK4(X1_58,X2_58,X3_58,X0_58),X0_60)
    | sP2(X1_58,X2_58,X3_58,X0_58) = iProver_top
    | v1_funct_1(sK4(X1_58,X2_58,X3_58,X0_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15761,c_15737])).

cnf(c_40,plain,
    ( sP2(X0,X1,X2,X3)
    | v1_funct_1(sK4(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_14276,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58)
    | v1_funct_1(sK4(X0_58,X1_58,X2_58,X3_58)) ),
    inference(subtyping,[status(esa)],[c_40])).

cnf(c_15763,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_1(sK4(X0_58,X1_58,X2_58,X3_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14276])).

cnf(c_28405,plain,
    ( k2_partfun1(u1_struct_0(X0_58),u1_struct_0(X1_58),sK4(X1_58,X2_58,X3_58,X0_58),X0_60) = k7_relat_1(sK4(X1_58,X2_58,X3_58,X0_58),X0_60)
    | sP2(X1_58,X2_58,X3_58,X0_58) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18338,c_15763])).

cnf(c_11,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_14304,plain,
    ( ~ v5_pre_topc(X0_59,X0_58,X1_58)
    | ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | v1_funct_2(k2_tmap_1(X0_58,X1_58,X0_59,X2_58),u1_struct_0(X2_58),u1_struct_0(X1_58))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ m1_pre_topc(X2_58,X0_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(X0_58)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X0_58)
    | ~ v1_funct_1(X0_59) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_15735,plain,
    ( v5_pre_topc(X0_59,X0_58,X1_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_58,X1_58,X0_59,X2_58),u1_struct_0(X2_58),u1_struct_0(X1_58)) = iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14304])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_14310,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | m1_subset_1(k2_tmap_1(X0_58,X1_58,X0_59,X2_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58))))
    | ~ l1_struct_0(X2_58)
    | ~ l1_struct_0(X1_58)
    | ~ l1_struct_0(X0_58)
    | ~ v1_funct_1(X0_59) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_15729,plain,
    ( v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_58,X1_58,X0_59,X2_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) = iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | l1_struct_0(X2_58) != iProver_top
    | l1_struct_0(X1_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14310])).

cnf(c_76,negated_conjecture,
    ( k1_tsep_1(sK7,sK8,sK9) = sK7 ),
    inference(cnf_transformation,[],[f150])).

cnf(c_14252,negated_conjecture,
    ( k1_tsep_1(sK7,sK8,sK9) = sK7 ),
    inference(subtyping,[status(esa)],[c_76])).

cnf(c_43,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X4,X1),X1,X0)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X4,X2),X2,X0)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X4,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X4,X2),u1_struct_0(X2),u1_struct_0(X0))
    | v1_funct_2(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X4,X1))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X4,X2)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_14273,plain,
    ( ~ sP2(X0_58,X1_58,X2_58,X3_58)
    | ~ v5_pre_topc(k2_tmap_1(X3_58,X0_58,X0_59,X1_58),X1_58,X0_58)
    | ~ v5_pre_topc(k2_tmap_1(X3_58,X0_58,X0_59,X2_58),X2_58,X0_58)
    | ~ v1_funct_2(X0_59,u1_struct_0(X3_58),u1_struct_0(X0_58))
    | ~ v1_funct_2(k2_tmap_1(X3_58,X0_58,X0_59,X1_58),u1_struct_0(X1_58),u1_struct_0(X0_58))
    | ~ v1_funct_2(k2_tmap_1(X3_58,X0_58,X0_59,X2_58),u1_struct_0(X2_58),u1_struct_0(X0_58))
    | v1_funct_2(k2_tmap_1(X3_58,X0_58,X0_59,k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X0_58))))
    | ~ m1_subset_1(k2_tmap_1(X3_58,X0_58,X0_59,X1_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58))))
    | ~ m1_subset_1(k2_tmap_1(X3_58,X0_58,X0_59,X2_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58))))
    | ~ v1_funct_1(X0_59)
    | ~ v1_funct_1(k2_tmap_1(X3_58,X0_58,X0_59,X1_58))
    | ~ v1_funct_1(k2_tmap_1(X3_58,X0_58,X0_59,X2_58)) ),
    inference(subtyping,[status(esa)],[c_43])).

cnf(c_15766,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58) != iProver_top
    | v5_pre_topc(k2_tmap_1(X3_58,X0_58,X0_59,X1_58),X1_58,X0_58) != iProver_top
    | v5_pre_topc(k2_tmap_1(X3_58,X0_58,X0_59,X2_58),X2_58,X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X3_58),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(X3_58,X0_58,X0_59,X1_58),u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(X3_58,X0_58,X0_59,X2_58),u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(X3_58,X0_58,X0_59,k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)) = iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X3_58,X0_58,X0_59,X1_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X3_58,X0_58,X0_59,X2_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k2_tmap_1(X3_58,X0_58,X0_59,X1_58)) != iProver_top
    | v1_funct_1(k2_tmap_1(X3_58,X0_58,X0_59,X2_58)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14273])).

cnf(c_26520,plain,
    ( sP2(X0_58,sK9,sK8,sK7) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK8),sK8,X0_58) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK9),sK9,X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(sK7),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK8),u1_struct_0(sK8),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK9),u1_struct_0(sK9),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK7),u1_struct_0(sK7),u1_struct_0(X0_58)) = iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK7,X0_58,X0_59,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK7,X0_58,X0_59,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK8)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14252,c_15766])).

cnf(c_27280,plain,
    ( sP2(X0_58,sK9,sK8,sK7) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK8),sK8,X0_58) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK9),sK9,X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(sK7),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK8),u1_struct_0(sK8),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK9),u1_struct_0(sK9),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK7),u1_struct_0(sK7),u1_struct_0(X0_58)) = iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK7,X0_58,X0_59,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X0_58)))) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | l1_struct_0(sK9) != iProver_top
    | l1_struct_0(sK7) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK8)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15729,c_26520])).

cnf(c_81,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_86,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_81])).

cnf(c_8,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_14307,plain,
    ( l1_struct_0(X0_58)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_16693,plain,
    ( l1_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_14307])).

cnf(c_16694,plain,
    ( l1_struct_0(sK7) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16693])).

cnf(c_77,negated_conjecture,
    ( m1_pre_topc(sK9,sK7) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_14251,negated_conjecture,
    ( m1_pre_topc(sK9,sK7) ),
    inference(subtyping,[status(esa)],[c_77])).

cnf(c_15787,plain,
    ( m1_pre_topc(sK9,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14251])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_14306,plain,
    ( ~ m1_pre_topc(X0_58,X1_58)
    | ~ l1_pre_topc(X1_58)
    | l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_15733,plain,
    ( m1_pre_topc(X0_58,X1_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14306])).

cnf(c_16900,plain,
    ( l1_pre_topc(sK9) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_15787,c_15733])).

cnf(c_16923,plain,
    ( l1_pre_topc(sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16900,c_86])).

cnf(c_15732,plain,
    ( l1_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14307])).

cnf(c_16928,plain,
    ( l1_struct_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_16923,c_15732])).

cnf(c_27429,plain,
    ( sP2(X0_58,sK9,sK8,sK7) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK8),sK8,X0_58) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK9),sK9,X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(sK7),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK8),u1_struct_0(sK8),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK9),u1_struct_0(sK9),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK7),u1_struct_0(sK7),u1_struct_0(X0_58)) = iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK7,X0_58,X0_59,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X0_58)))) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK8)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27280,c_86,c_16694,c_16928])).

cnf(c_27452,plain,
    ( sP2(X0_58,sK9,sK8,sK7) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK8),sK8,X0_58) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK9),sK9,X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(sK7),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK8),u1_struct_0(sK8),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK9),u1_struct_0(sK9),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK7),u1_struct_0(sK7),u1_struct_0(X0_58)) = iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0_58)))) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | l1_struct_0(sK8) != iProver_top
    | l1_struct_0(sK7) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK8)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15729,c_27429])).

cnf(c_79,negated_conjecture,
    ( m1_pre_topc(sK8,sK7) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_88,plain,
    ( m1_pre_topc(sK8,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_79])).

cnf(c_248,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_250,plain,
    ( l1_struct_0(sK8) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_16705,plain,
    ( ~ m1_pre_topc(X0_58,sK7)
    | l1_pre_topc(X0_58)
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_14306])).

cnf(c_16706,plain,
    ( m1_pre_topc(X0_58,sK7) != iProver_top
    | l1_pre_topc(X0_58) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16705])).

cnf(c_16708,plain,
    ( m1_pre_topc(sK8,sK7) != iProver_top
    | l1_pre_topc(sK8) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_16706])).

cnf(c_27899,plain,
    ( sP2(X0_58,sK9,sK8,sK7) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK8),sK8,X0_58) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK9),sK9,X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(sK7),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK8),u1_struct_0(sK8),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK9),u1_struct_0(sK9),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK7),u1_struct_0(sK7),u1_struct_0(X0_58)) = iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0_58)))) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK8)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27452,c_86,c_88,c_250,c_16694,c_16708])).

cnf(c_27921,plain,
    ( sP2(X0_58,sK9,sK8,sK7) != iProver_top
    | v5_pre_topc(X0_59,sK7,X0_58) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK8),sK8,X0_58) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK9),sK9,X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(sK7),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK8),u1_struct_0(sK8),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK7),u1_struct_0(sK7),u1_struct_0(X0_58)) = iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0_58)))) != iProver_top
    | m1_pre_topc(sK9,sK7) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK8)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15735,c_27899])).

cnf(c_14386,plain,
    ( l1_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14307])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_14309,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | v1_funct_2(k2_tmap_1(X0_58,X1_58,X0_59,X2_58),u1_struct_0(X2_58),u1_struct_0(X1_58))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ l1_struct_0(X2_58)
    | ~ l1_struct_0(X1_58)
    | ~ l1_struct_0(X0_58)
    | ~ v1_funct_1(X0_59) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_15730,plain,
    ( v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_58,X1_58,X0_59,X2_58),u1_struct_0(X2_58),u1_struct_0(X1_58)) = iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | l1_struct_0(X2_58) != iProver_top
    | l1_struct_0(X1_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14309])).

cnf(c_27922,plain,
    ( sP2(X0_58,sK9,sK8,sK7) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK8),sK8,X0_58) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK9),sK9,X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(sK7),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK8),u1_struct_0(sK8),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK7),u1_struct_0(sK7),u1_struct_0(X0_58)) = iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0_58)))) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | l1_struct_0(sK9) != iProver_top
    | l1_struct_0(sK7) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK8)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15730,c_27899])).

cnf(c_28696,plain,
    ( sP2(X0_58,sK9,sK8,sK7) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK8),sK8,X0_58) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK9),sK9,X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(sK7),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK8),u1_struct_0(sK8),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK7),u1_struct_0(sK7),u1_struct_0(X0_58)) = iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0_58)))) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK8)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27922,c_86,c_16694,c_16928])).

cnf(c_28718,plain,
    ( sP2(X0_58,sK9,sK8,sK7) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK8),sK8,X0_58) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK9),sK9,X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(sK7),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK7),u1_struct_0(sK7),u1_struct_0(X0_58)) = iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0_58)))) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | l1_struct_0(sK8) != iProver_top
    | l1_struct_0(sK7) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK8)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15730,c_28696])).

cnf(c_42155,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(sK7),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK9),sK9,X0_58) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK8),sK8,X0_58) != iProver_top
    | sP2(X0_58,sK9,sK8,sK7) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK7),u1_struct_0(sK7),u1_struct_0(X0_58)) = iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK8)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27921,c_86,c_88,c_250,c_14386,c_16694,c_16708,c_28718])).

cnf(c_42156,plain,
    ( sP2(X0_58,sK9,sK8,sK7) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK8),sK8,X0_58) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,X0_59,sK9),sK9,X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(sK7),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,X0_59,sK7),u1_struct_0(sK7),u1_struct_0(X0_58)) = iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0_58)))) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK8)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,X0_59,sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_42155])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_14314,plain,
    ( ~ m1_pre_topc(X0_58,X1_58)
    | ~ m1_pre_topc(X2_58,X1_58)
    | m1_pre_topc(k1_tsep_1(X1_58,X2_58,X0_58),X1_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | ~ l1_pre_topc(X1_58) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_15725,plain,
    ( m1_pre_topc(X0_58,X1_58) != iProver_top
    | m1_pre_topc(X2_58,X1_58) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1_58,X2_58,X0_58),X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | l1_pre_topc(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14314])).

cnf(c_16958,plain,
    ( m1_pre_topc(sK8,sK7) != iProver_top
    | m1_pre_topc(sK9,sK7) != iProver_top
    | m1_pre_topc(sK7,sK7) = iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_14252,c_15725])).

cnf(c_83,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_84,plain,
    ( v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_83])).

cnf(c_80,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_87,plain,
    ( v2_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_80])).

cnf(c_78,negated_conjecture,
    ( ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_89,plain,
    ( v2_struct_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_78])).

cnf(c_90,plain,
    ( m1_pre_topc(sK9,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_77])).

cnf(c_17146,plain,
    ( m1_pre_topc(sK7,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16958,c_84,c_86,c_87,c_88,c_89,c_90])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_14315,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ m1_pre_topc(X2_58,X0_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(X0_58)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X0_58)
    | ~ v1_funct_1(X0_59)
    | k2_partfun1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_59,u1_struct_0(X2_58)) = k2_tmap_1(X0_58,X1_58,X0_59,X2_58) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_15724,plain,
    ( k2_partfun1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_59,u1_struct_0(X2_58)) = k2_tmap_1(X0_58,X1_58,X0_59,X2_58)
    | v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14315])).

cnf(c_18342,plain,
    ( k2_partfun1(u1_struct_0(X0_58),u1_struct_0(X1_58),sK4(X1_58,X2_58,X3_58,X0_58),u1_struct_0(X4_58)) = k2_tmap_1(X0_58,X1_58,sK4(X1_58,X2_58,X3_58,X0_58),X4_58)
    | sP2(X1_58,X2_58,X3_58,X0_58) = iProver_top
    | v1_funct_2(sK4(X1_58,X2_58,X3_58,X0_58),u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | m1_pre_topc(X4_58,X0_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v1_funct_1(sK4(X1_58,X2_58,X3_58,X0_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15761,c_15724])).

cnf(c_39,plain,
    ( sP2(X0,X1,X2,X3)
    | v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_14277,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58)
    | v1_funct_2(sK4(X0_58,X1_58,X2_58,X3_58),u1_struct_0(X3_58),u1_struct_0(X0_58)) ),
    inference(subtyping,[status(esa)],[c_39])).

cnf(c_15762,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_2(sK4(X0_58,X1_58,X2_58,X3_58),u1_struct_0(X3_58),u1_struct_0(X0_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14277])).

cnf(c_36657,plain,
    ( k2_partfun1(u1_struct_0(X0_58),u1_struct_0(X1_58),sK4(X1_58,X2_58,X3_58,X0_58),u1_struct_0(X4_58)) = k2_tmap_1(X0_58,X1_58,sK4(X1_58,X2_58,X3_58,X0_58),X4_58)
    | sP2(X1_58,X2_58,X3_58,X0_58) = iProver_top
    | m1_pre_topc(X4_58,X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18342,c_15763,c_15762])).

cnf(c_36664,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(X0_58),sK4(X0_58,X1_58,X2_58,sK7),u1_struct_0(sK7)) = k2_tmap_1(sK7,X0_58,sK4(X0_58,X1_58,X2_58,sK7),sK7)
    | sP2(X0_58,X1_58,X2_58,sK7) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_17146,c_36657])).

cnf(c_82,negated_conjecture,
    ( v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_85,plain,
    ( v2_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_82])).

cnf(c_36843,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | sP2(X0_58,X1_58,X2_58,sK7) = iProver_top
    | k2_partfun1(u1_struct_0(sK7),u1_struct_0(X0_58),sK4(X0_58,X1_58,X2_58,sK7),u1_struct_0(sK7)) = k2_tmap_1(sK7,X0_58,sK4(X0_58,X1_58,X2_58,sK7),sK7)
    | v2_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_36664,c_84,c_85,c_86])).

cnf(c_36844,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(X0_58),sK4(X0_58,X1_58,X2_58,sK7),u1_struct_0(sK7)) = k2_tmap_1(sK7,X0_58,sK4(X0_58,X1_58,X2_58,sK7),sK7)
    | sP2(X0_58,X1_58,X2_58,sK7) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_36843])).

cnf(c_45,plain,
    ( ~ sP2(sK5(X0,X1,X2),X2,X1,X0)
    | r3_tsep_1(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_14271,plain,
    ( ~ sP2(sK5(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58)
    | r3_tsep_1(X0_58,X1_58,X2_58)
    | ~ r1_tsep_1(X1_58,X2_58)
    | ~ m1_pre_topc(X2_58,X0_58)
    | ~ m1_pre_topc(X1_58,X0_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | ~ v2_pre_topc(X0_58)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_45])).

cnf(c_15768,plain,
    ( sP2(sK5(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58) != iProver_top
    | r3_tsep_1(X0_58,X1_58,X2_58) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14271])).

cnf(c_36854,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,X0_58,X1_58)),sK4(sK5(sK7,X0_58,X1_58),X1_58,X0_58,sK7),u1_struct_0(sK7)) = k2_tmap_1(sK7,sK5(sK7,X0_58,X1_58),sK4(sK5(sK7,X0_58,X1_58),X1_58,X0_58,sK7),sK7)
    | r3_tsep_1(sK7,X0_58,X1_58) = iProver_top
    | r1_tsep_1(X0_58,X1_58) != iProver_top
    | m1_pre_topc(X0_58,sK7) != iProver_top
    | m1_pre_topc(X1_58,sK7) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(sK5(sK7,X0_58,X1_58)) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(sK5(sK7,X0_58,X1_58)) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK5(sK7,X0_58,X1_58)) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_36844,c_15768])).

cnf(c_48,plain,
    ( r3_tsep_1(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_struct_0(sK5(X0,X1,X2))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_14268,plain,
    ( r3_tsep_1(X0_58,X1_58,X2_58)
    | ~ r1_tsep_1(X1_58,X2_58)
    | ~ m1_pre_topc(X2_58,X0_58)
    | ~ m1_pre_topc(X1_58,X0_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | ~ v2_struct_0(sK5(X0_58,X1_58,X2_58))
    | ~ v2_pre_topc(X0_58)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_48])).

cnf(c_16805,plain,
    ( r3_tsep_1(sK7,X0_58,X1_58)
    | ~ r1_tsep_1(X0_58,X1_58)
    | ~ m1_pre_topc(X0_58,sK7)
    | ~ m1_pre_topc(X1_58,sK7)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | ~ v2_struct_0(sK5(sK7,X0_58,X1_58))
    | v2_struct_0(sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_14268])).

cnf(c_16806,plain,
    ( r3_tsep_1(sK7,X0_58,X1_58) = iProver_top
    | r1_tsep_1(X0_58,X1_58) != iProver_top
    | m1_pre_topc(X0_58,sK7) != iProver_top
    | m1_pre_topc(X1_58,sK7) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(sK5(sK7,X0_58,X1_58)) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16805])).

cnf(c_47,plain,
    ( r3_tsep_1(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK5(X0,X1,X2))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_14269,plain,
    ( r3_tsep_1(X0_58,X1_58,X2_58)
    | ~ r1_tsep_1(X1_58,X2_58)
    | ~ m1_pre_topc(X2_58,X0_58)
    | ~ m1_pre_topc(X1_58,X0_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | ~ v2_pre_topc(X0_58)
    | v2_pre_topc(sK5(X0_58,X1_58,X2_58))
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_47])).

cnf(c_16815,plain,
    ( r3_tsep_1(sK7,X0_58,X1_58)
    | ~ r1_tsep_1(X0_58,X1_58)
    | ~ m1_pre_topc(X0_58,sK7)
    | ~ m1_pre_topc(X1_58,sK7)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(sK7)
    | v2_pre_topc(sK5(sK7,X0_58,X1_58))
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_14269])).

cnf(c_16816,plain,
    ( r3_tsep_1(sK7,X0_58,X1_58) = iProver_top
    | r1_tsep_1(X0_58,X1_58) != iProver_top
    | m1_pre_topc(X0_58,sK7) != iProver_top
    | m1_pre_topc(X1_58,sK7) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(sK5(sK7,X0_58,X1_58)) = iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16815])).

cnf(c_46,plain,
    ( r3_tsep_1(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK5(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_14270,plain,
    ( r3_tsep_1(X0_58,X1_58,X2_58)
    | ~ r1_tsep_1(X1_58,X2_58)
    | ~ m1_pre_topc(X2_58,X0_58)
    | ~ m1_pre_topc(X1_58,X0_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | ~ v2_pre_topc(X0_58)
    | ~ l1_pre_topc(X0_58)
    | l1_pre_topc(sK5(X0_58,X1_58,X2_58)) ),
    inference(subtyping,[status(esa)],[c_46])).

cnf(c_16825,plain,
    ( r3_tsep_1(sK7,X0_58,X1_58)
    | ~ r1_tsep_1(X0_58,X1_58)
    | ~ m1_pre_topc(X0_58,sK7)
    | ~ m1_pre_topc(X1_58,sK7)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(sK7)
    | ~ v2_pre_topc(sK7)
    | l1_pre_topc(sK5(sK7,X0_58,X1_58))
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_14270])).

cnf(c_16826,plain,
    ( r3_tsep_1(sK7,X0_58,X1_58) = iProver_top
    | r1_tsep_1(X0_58,X1_58) != iProver_top
    | m1_pre_topc(X0_58,sK7) != iProver_top
    | m1_pre_topc(X1_58,sK7) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK5(sK7,X0_58,X1_58)) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16825])).

cnf(c_36980,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,X0_58,X1_58)),sK4(sK5(sK7,X0_58,X1_58),X1_58,X0_58,sK7),u1_struct_0(sK7)) = k2_tmap_1(sK7,sK5(sK7,X0_58,X1_58),sK4(sK5(sK7,X0_58,X1_58),X1_58,X0_58,sK7),sK7)
    | r3_tsep_1(sK7,X0_58,X1_58) = iProver_top
    | r1_tsep_1(X0_58,X1_58) != iProver_top
    | m1_pre_topc(X0_58,sK7) != iProver_top
    | m1_pre_topc(X1_58,sK7) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_36854,c_84,c_85,c_86,c_16806,c_16816,c_16826])).

cnf(c_63,plain,
    ( sP3(X0,X1,X2,X3)
    | m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_14257,plain,
    ( sP3(X0_58,X1_58,X2_58,X3_58)
    | m1_subset_1(sK6(X0_58,X1_58,X2_58,X3_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) ),
    inference(subtyping,[status(esa)],[c_63])).

cnf(c_15782,plain,
    ( sP3(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | m1_subset_1(sK6(X0_58,X1_58,X2_58,X3_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14257])).

cnf(c_18561,plain,
    ( k2_partfun1(u1_struct_0(X0_58),u1_struct_0(X1_58),sK6(X1_58,X0_58,X2_58,X3_58),X0_60) = k7_relat_1(sK6(X1_58,X0_58,X2_58,X3_58),X0_60)
    | sP3(X1_58,X0_58,X2_58,X3_58) = iProver_top
    | v1_funct_1(sK6(X1_58,X0_58,X2_58,X3_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15782,c_15737])).

cnf(c_65,plain,
    ( sP3(X0,X1,X2,X3)
    | v1_funct_1(sK6(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_14255,plain,
    ( sP3(X0_58,X1_58,X2_58,X3_58)
    | v1_funct_1(sK6(X0_58,X1_58,X2_58,X3_58)) ),
    inference(subtyping,[status(esa)],[c_65])).

cnf(c_15784,plain,
    ( sP3(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_1(sK6(X0_58,X1_58,X2_58,X3_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14255])).

cnf(c_28417,plain,
    ( k2_partfun1(u1_struct_0(X0_58),u1_struct_0(X1_58),sK6(X1_58,X0_58,X2_58,X3_58),X0_60) = k7_relat_1(sK6(X1_58,X0_58,X2_58,X3_58),X0_60)
    | sP3(X1_58,X0_58,X2_58,X3_58) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18561,c_15784])).

cnf(c_50,plain,
    ( ~ r3_tsep_1(X0,X1,X2)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_75,negated_conjecture,
    ( r3_tsep_1(sK7,sK8,sK9)
    | r1_tsep_1(sK8,sK9) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_3364,plain,
    ( r1_tsep_1(X0,X1)
    | r1_tsep_1(sK8,sK9)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | sK8 != X0
    | sK9 != X1
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_50,c_75])).

cnf(c_3365,plain,
    ( r1_tsep_1(sK8,sK9)
    | ~ m1_pre_topc(sK8,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v2_struct_0(sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_3364])).

cnf(c_3367,plain,
    ( r1_tsep_1(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3365,c_83,c_82,c_81,c_80,c_79,c_78,c_77])).

cnf(c_70,negated_conjecture,
    ( ~ sP3(sK10,sK7,sK9,sK8)
    | ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9) ),
    inference(cnf_transformation,[],[f156])).

cnf(c_3740,plain,
    ( ~ sP3(sK10,sK7,sK9,sK8)
    | ~ r3_tsep_1(sK7,sK8,sK9) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3367,c_70])).

cnf(c_14241,plain,
    ( ~ sP3(sK10,sK7,sK9,sK8)
    | ~ r3_tsep_1(sK7,sK8,sK9) ),
    inference(subtyping,[status(esa)],[c_3740])).

cnf(c_15797,plain,
    ( sP3(sK10,sK7,sK9,sK8) != iProver_top
    | r3_tsep_1(sK7,sK8,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14241])).

cnf(c_28421,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK10),sK6(sK10,sK7,sK9,sK8),X0_60) = k7_relat_1(sK6(sK10,sK7,sK9,sK8),X0_60)
    | r3_tsep_1(sK7,sK8,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_28417,c_15797])).

cnf(c_73,negated_conjecture,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f153])).

cnf(c_95,plain,
    ( r3_tsep_1(sK7,sK8,sK9) != iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top
    | v2_struct_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_72,negated_conjecture,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | v2_pre_topc(sK10) ),
    inference(cnf_transformation,[],[f154])).

cnf(c_96,plain,
    ( r3_tsep_1(sK7,sK8,sK9) != iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top
    | v2_pre_topc(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_72])).

cnf(c_71,negated_conjecture,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | l1_pre_topc(sK10) ),
    inference(cnf_transformation,[],[f155])).

cnf(c_97,plain,
    ( r3_tsep_1(sK7,sK8,sK9) != iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top
    | l1_pre_topc(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_54,plain,
    ( sP3(X0,X1,X2,X3)
    | ~ v5_pre_topc(sK6(X0,X1,X2,X3),X1,X0)
    | ~ v1_funct_2(sK6(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ v1_funct_1(sK6(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_64,plain,
    ( sP3(X0,X1,X2,X3)
    | v1_funct_2(sK6(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_467,plain,
    ( ~ v5_pre_topc(sK6(X0,X1,X2,X3),X1,X0)
    | sP3(X0,X1,X2,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_54,c_65,c_64,c_63])).

cnf(c_468,plain,
    ( sP3(X0,X1,X2,X3)
    | ~ v5_pre_topc(sK6(X0,X1,X2,X3),X1,X0) ),
    inference(renaming,[status(thm)],[c_467])).

cnf(c_2564,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ v5_pre_topc(sK6(X0,X1,X2,X3),X1,X0)
    | ~ r1_tsep_1(sK8,sK9)
    | sK8 != X3
    | sK9 != X2
    | sK7 != X1
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_468,c_70])).

cnf(c_2565,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ v5_pre_topc(sK6(sK10,sK7,sK9,sK8),sK7,sK10)
    | ~ r1_tsep_1(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2564])).

cnf(c_2566,plain,
    ( r3_tsep_1(sK7,sK8,sK9) != iProver_top
    | v5_pre_topc(sK6(sK10,sK7,sK9,sK8),sK7,sK10) != iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2565])).

cnf(c_2577,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | v1_funct_1(sK6(X0,X1,X2,X3))
    | sK8 != X3
    | sK9 != X2
    | sK7 != X1
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_65,c_70])).

cnf(c_2578,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | v1_funct_1(sK6(sK10,sK7,sK9,sK8)) ),
    inference(unflattening,[status(thm)],[c_2577])).

cnf(c_2579,plain,
    ( r3_tsep_1(sK7,sK8,sK9) != iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top
    | v1_funct_1(sK6(sK10,sK7,sK9,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2578])).

cnf(c_2590,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | v1_funct_2(sK6(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
    | ~ r1_tsep_1(sK8,sK9)
    | sK8 != X3
    | sK9 != X2
    | sK7 != X1
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_64,c_70])).

cnf(c_2591,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | v1_funct_2(sK6(sK10,sK7,sK9,sK8),u1_struct_0(sK7),u1_struct_0(sK10))
    | ~ r1_tsep_1(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2590])).

cnf(c_2592,plain,
    ( r3_tsep_1(sK7,sK8,sK9) != iProver_top
    | v1_funct_2(sK6(sK10,sK7,sK9,sK8),u1_struct_0(sK7),u1_struct_0(sK10)) = iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2591])).

cnf(c_2603,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | sK8 != X3
    | sK9 != X2
    | sK7 != X1
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_63,c_70])).

cnf(c_2604,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | m1_subset_1(sK6(sK10,sK7,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK10)))) ),
    inference(unflattening,[status(thm)],[c_2603])).

cnf(c_2605,plain,
    ( r3_tsep_1(sK7,sK8,sK9) != iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top
    | m1_subset_1(sK6(sK10,sK7,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK10)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2604])).

cnf(c_62,plain,
    ( sP3(X0,X1,X2,X3)
    | v1_funct_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3)) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_2616,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | v1_funct_1(k2_tmap_1(X0,X1,sK6(X1,X0,X2,X3),X3))
    | sK8 != X3
    | sK9 != X2
    | sK7 != X0
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_62,c_70])).

cnf(c_2617,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | v1_funct_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8)) ),
    inference(unflattening,[status(thm)],[c_2616])).

cnf(c_2618,plain,
    ( r3_tsep_1(sK7,sK8,sK9) != iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2617])).

cnf(c_61,plain,
    ( sP3(X0,X1,X2,X3)
    | v1_funct_2(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3),u1_struct_0(X3),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_2629,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | v1_funct_2(k2_tmap_1(X0,X1,sK6(X1,X0,X2,X3),X3),u1_struct_0(X3),u1_struct_0(X1))
    | ~ r1_tsep_1(sK8,sK9)
    | sK8 != X3
    | sK9 != X2
    | sK7 != X0
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_61,c_70])).

cnf(c_2630,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | v1_funct_2(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8),u1_struct_0(sK8),u1_struct_0(sK10))
    | ~ r1_tsep_1(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2629])).

cnf(c_2631,plain,
    ( r3_tsep_1(sK7,sK8,sK9) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8),u1_struct_0(sK8),u1_struct_0(sK10)) = iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2630])).

cnf(c_60,plain,
    ( sP3(X0,X1,X2,X3)
    | v5_pre_topc(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3),X3,X0) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_2642,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | v5_pre_topc(k2_tmap_1(X0,X1,sK6(X1,X0,X2,X3),X3),X3,X1)
    | ~ r1_tsep_1(sK8,sK9)
    | sK8 != X3
    | sK9 != X2
    | sK7 != X0
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_60,c_70])).

cnf(c_2643,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | v5_pre_topc(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8),sK8,sK10)
    | ~ r1_tsep_1(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2642])).

cnf(c_2644,plain,
    ( r3_tsep_1(sK7,sK8,sK9) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8),sK8,sK10) = iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2643])).

cnf(c_59,plain,
    ( sP3(X0,X1,X2,X3)
    | m1_subset_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_2655,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | m1_subset_1(k2_tmap_1(X0,X1,sK6(X1,X0,X2,X3),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | sK8 != X3
    | sK9 != X2
    | sK7 != X0
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_59,c_70])).

cnf(c_2656,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | m1_subset_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK10)))) ),
    inference(unflattening,[status(thm)],[c_2655])).

cnf(c_2657,plain,
    ( r3_tsep_1(sK7,sK8,sK9) != iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top
    | m1_subset_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK10)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2656])).

cnf(c_58,plain,
    ( sP3(X0,X1,X2,X3)
    | v1_funct_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2)) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_2668,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | v1_funct_1(k2_tmap_1(X0,X1,sK6(X1,X0,X2,X3),X2))
    | sK8 != X3
    | sK9 != X2
    | sK7 != X0
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_58,c_70])).

cnf(c_2669,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | v1_funct_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9)) ),
    inference(unflattening,[status(thm)],[c_2668])).

cnf(c_2670,plain,
    ( r3_tsep_1(sK7,sK8,sK9) != iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2669])).

cnf(c_57,plain,
    ( sP3(X0,X1,X2,X3)
    | v1_funct_2(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_2681,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | v1_funct_2(k2_tmap_1(X0,X1,sK6(X1,X0,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X1))
    | ~ r1_tsep_1(sK8,sK9)
    | sK8 != X3
    | sK9 != X2
    | sK7 != X0
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_57,c_70])).

cnf(c_2682,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | v1_funct_2(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),u1_struct_0(sK9),u1_struct_0(sK10))
    | ~ r1_tsep_1(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2681])).

cnf(c_2683,plain,
    ( r3_tsep_1(sK7,sK8,sK9) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),u1_struct_0(sK9),u1_struct_0(sK10)) = iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2682])).

cnf(c_56,plain,
    ( sP3(X0,X1,X2,X3)
    | v5_pre_topc(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2),X2,X0) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_2694,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | v5_pre_topc(k2_tmap_1(X0,X1,sK6(X1,X0,X2,X3),X2),X2,X1)
    | ~ r1_tsep_1(sK8,sK9)
    | sK8 != X3
    | sK9 != X2
    | sK7 != X0
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_56,c_70])).

cnf(c_2695,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | v5_pre_topc(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),sK9,sK10)
    | ~ r1_tsep_1(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2694])).

cnf(c_2696,plain,
    ( r3_tsep_1(sK7,sK8,sK9) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),sK9,sK10) = iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2695])).

cnf(c_55,plain,
    ( sP3(X0,X1,X2,X3)
    | m1_subset_1(k2_tmap_1(X1,X0,sK6(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_2707,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | m1_subset_1(k2_tmap_1(X0,X1,sK6(X1,X0,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | sK8 != X3
    | sK9 != X2
    | sK7 != X0
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_55,c_70])).

cnf(c_2708,plain,
    ( ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | m1_subset_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK10)))) ),
    inference(unflattening,[status(thm)],[c_2707])).

cnf(c_2709,plain,
    ( r3_tsep_1(sK7,sK8,sK9) != iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top
    | m1_subset_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK10)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2708])).

cnf(c_3366,plain,
    ( r1_tsep_1(sK8,sK9) = iProver_top
    | m1_pre_topc(sK8,sK7) != iProver_top
    | m1_pre_topc(sK9,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3365])).

cnf(c_19,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_14296,plain,
    ( sP0(X0_58,X1_58,X0_59,X2_58,X3_58)
    | ~ v5_pre_topc(k2_tmap_1(X2_58,X0_58,X0_59,X1_58),X1_58,X0_58)
    | ~ v5_pre_topc(k2_tmap_1(X2_58,X0_58,X0_59,X3_58),X3_58,X0_58)
    | ~ v1_funct_2(k2_tmap_1(X2_58,X0_58,X0_59,X1_58),u1_struct_0(X1_58),u1_struct_0(X0_58))
    | ~ v1_funct_2(k2_tmap_1(X2_58,X0_58,X0_59,X3_58),u1_struct_0(X3_58),u1_struct_0(X0_58))
    | ~ m1_subset_1(k2_tmap_1(X2_58,X0_58,X0_59,X1_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58))))
    | ~ m1_subset_1(k2_tmap_1(X2_58,X0_58,X0_59,X3_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X0_58))))
    | ~ v1_funct_1(k2_tmap_1(X2_58,X0_58,X0_59,X1_58))
    | ~ v1_funct_1(k2_tmap_1(X2_58,X0_58,X0_59,X3_58)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_18976,plain,
    ( sP0(sK10,sK9,sK6(sK10,sK7,sK9,sK8),sK7,X0_58)
    | ~ v5_pre_topc(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),X0_58),X0_58,sK10)
    | ~ v5_pre_topc(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),sK9,sK10)
    | ~ v1_funct_2(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),X0_58),u1_struct_0(X0_58),u1_struct_0(sK10))
    | ~ v1_funct_2(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),u1_struct_0(sK9),u1_struct_0(sK10))
    | ~ m1_subset_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK10))))
    | ~ m1_subset_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK10))))
    | ~ v1_funct_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),X0_58))
    | ~ v1_funct_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9)) ),
    inference(instantiation,[status(thm)],[c_14296])).

cnf(c_18977,plain,
    ( sP0(sK10,sK9,sK6(sK10,sK7,sK9,sK8),sK7,X0_58) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),X0_58),X0_58,sK10) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),sK9,sK10) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),X0_58),u1_struct_0(X0_58),u1_struct_0(sK10)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),u1_struct_0(sK9),u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK10)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK10)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),X0_58)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18976])).

cnf(c_18979,plain,
    ( sP0(sK10,sK9,sK6(sK10,sK7,sK9,sK8),sK7,sK8) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8),sK8,sK10) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),sK9,sK10) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8),u1_struct_0(sK8),u1_struct_0(sK10)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),u1_struct_0(sK9),u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK10)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK10)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK8)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,sK10,sK6(sK10,sK7,sK9,sK8),sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_18977])).

cnf(c_28,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ r4_tsep_1(X1,X0,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | k1_tsep_1(X1,X0,X3) != X1 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_51,plain,
    ( ~ r3_tsep_1(X0,X1,X2)
    | r4_tsep_1(X0,X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_898,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ r3_tsep_1(X5,X6,X7)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X7,X5)
    | ~ m1_pre_topc(X6,X5)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | v2_struct_0(X6)
    | v2_struct_0(X7)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X5)
    | ~ v1_funct_1(X2)
    | X5 != X1
    | X7 != X3
    | X6 != X0
    | k1_tsep_1(X1,X0,X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_51])).

cnf(c_899,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ r3_tsep_1(X1,X0,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X2)
    | k1_tsep_1(X1,X0,X3) != X1 ),
    inference(unflattening,[status(thm)],[c_898])).

cnf(c_14243,plain,
    ( sP1(X0_58,X1_58,X0_59,X2_58,X3_58)
    | ~ r3_tsep_1(X1_58,X0_58,X2_58)
    | ~ v1_funct_2(X0_59,u1_struct_0(X1_58),u1_struct_0(X3_58))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X3_58))))
    | ~ m1_pre_topc(X0_58,X1_58)
    | ~ m1_pre_topc(X2_58,X1_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X3_58)
    | v2_struct_0(X2_58)
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(X3_58)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X3_58)
    | ~ v1_funct_1(X0_59)
    | k1_tsep_1(X1_58,X0_58,X2_58) != X1_58 ),
    inference(subtyping,[status(esa)],[c_899])).

cnf(c_16891,plain,
    ( sP1(X0_58,sK7,X0_59,X1_58,X2_58)
    | ~ r3_tsep_1(sK7,X0_58,X1_58)
    | ~ v1_funct_2(X0_59,u1_struct_0(sK7),u1_struct_0(X2_58))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X2_58))))
    | ~ m1_pre_topc(X0_58,sK7)
    | ~ m1_pre_topc(X1_58,sK7)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(sK7)
    | ~ v2_pre_topc(X2_58)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(X2_58)
    | ~ l1_pre_topc(sK7)
    | ~ v1_funct_1(X0_59)
    | k1_tsep_1(sK7,X0_58,X1_58) != sK7 ),
    inference(instantiation,[status(thm)],[c_14243])).

cnf(c_17082,plain,
    ( sP1(X0_58,sK7,X0_59,X1_58,sK10)
    | ~ r3_tsep_1(sK7,X0_58,X1_58)
    | ~ v1_funct_2(X0_59,u1_struct_0(sK7),u1_struct_0(sK10))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK10))))
    | ~ m1_pre_topc(X0_58,sK7)
    | ~ m1_pre_topc(X1_58,sK7)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(sK7)
    | v2_struct_0(sK10)
    | ~ v2_pre_topc(sK7)
    | ~ v2_pre_topc(sK10)
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK10)
    | ~ v1_funct_1(X0_59)
    | k1_tsep_1(sK7,X0_58,X1_58) != sK7 ),
    inference(instantiation,[status(thm)],[c_16891])).

cnf(c_18717,plain,
    ( sP1(X0_58,sK7,sK6(sK10,sK7,sK9,sK8),X1_58,sK10)
    | ~ r3_tsep_1(sK7,X0_58,X1_58)
    | ~ v1_funct_2(sK6(sK10,sK7,sK9,sK8),u1_struct_0(sK7),u1_struct_0(sK10))
    | ~ m1_subset_1(sK6(sK10,sK7,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK10))))
    | ~ m1_pre_topc(X0_58,sK7)
    | ~ m1_pre_topc(X1_58,sK7)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(sK7)
    | v2_struct_0(sK10)
    | ~ v2_pre_topc(sK7)
    | ~ v2_pre_topc(sK10)
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK10)
    | ~ v1_funct_1(sK6(sK10,sK7,sK9,sK8))
    | k1_tsep_1(sK7,X0_58,X1_58) != sK7 ),
    inference(instantiation,[status(thm)],[c_17082])).

cnf(c_23360,plain,
    ( sP1(sK8,sK7,sK6(sK10,sK7,sK9,sK8),sK9,sK10)
    | ~ r3_tsep_1(sK7,sK8,sK9)
    | ~ v1_funct_2(sK6(sK10,sK7,sK9,sK8),u1_struct_0(sK7),u1_struct_0(sK10))
    | ~ m1_subset_1(sK6(sK10,sK7,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK10))))
    | ~ m1_pre_topc(sK8,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v2_struct_0(sK7)
    | v2_struct_0(sK10)
    | ~ v2_pre_topc(sK7)
    | ~ v2_pre_topc(sK10)
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK10)
    | ~ v1_funct_1(sK6(sK10,sK7,sK9,sK8))
    | k1_tsep_1(sK7,sK8,sK9) != sK7 ),
    inference(instantiation,[status(thm)],[c_18717])).

cnf(c_23361,plain,
    ( k1_tsep_1(sK7,sK8,sK9) != sK7
    | sP1(sK8,sK7,sK6(sK10,sK7,sK9,sK8),sK9,sK10) = iProver_top
    | r3_tsep_1(sK7,sK8,sK9) != iProver_top
    | v1_funct_2(sK6(sK10,sK7,sK9,sK8),u1_struct_0(sK7),u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(sK6(sK10,sK7,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK10)))) != iProver_top
    | m1_pre_topc(sK8,sK7) != iProver_top
    | m1_pre_topc(sK9,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK10) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK10) != iProver_top
    | v1_funct_1(sK6(sK10,sK7,sK9,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23360])).

cnf(c_15,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(X2,X1,X4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_14300,plain,
    ( ~ sP1(X0_58,X1_58,X0_59,X2_58,X3_58)
    | ~ sP0(X3_58,X2_58,X0_59,X1_58,X0_58)
    | v5_pre_topc(X0_59,X1_58,X3_58) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_24714,plain,
    ( ~ sP1(sK8,sK7,sK6(sK10,sK7,sK9,sK8),sK9,sK10)
    | ~ sP0(sK10,sK9,sK6(sK10,sK7,sK9,sK8),sK7,sK8)
    | v5_pre_topc(sK6(sK10,sK7,sK9,sK8),sK7,sK10) ),
    inference(instantiation,[status(thm)],[c_14300])).

cnf(c_24721,plain,
    ( sP1(sK8,sK7,sK6(sK10,sK7,sK9,sK8),sK9,sK10) != iProver_top
    | sP0(sK10,sK9,sK6(sK10,sK7,sK9,sK8),sK7,sK8) != iProver_top
    | v5_pre_topc(sK6(sK10,sK7,sK9,sK8),sK7,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24714])).

cnf(c_28442,plain,
    ( r3_tsep_1(sK7,sK8,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28421,c_84,c_85,c_86,c_87,c_88,c_89,c_90,c_95,c_96,c_97,c_2566,c_2579,c_2592,c_2605,c_2618,c_2631,c_2644,c_2657,c_2670,c_2683,c_2696,c_2709,c_3366,c_14252,c_18979,c_23361,c_24721])).

cnf(c_36993,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK7)) = k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7)
    | r1_tsep_1(sK8,sK9) != iProver_top
    | m1_pre_topc(sK8,sK7) != iProver_top
    | m1_pre_topc(sK9,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_36980,c_28442])).

cnf(c_37669,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK7)) = k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_36993,c_84,c_85,c_86,c_87,c_88,c_89,c_90,c_3366])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_14312,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
    | m1_subset_1(k2_partfun1(X0_60,X1_60,X0_59,X2_60),k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
    | ~ v1_funct_1(X0_59) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_15727,plain,
    ( m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60))) != iProver_top
    | m1_subset_1(k2_partfun1(X0_60,X1_60,X0_59,X2_60),k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60))) = iProver_top
    | v1_funct_1(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14312])).

cnf(c_37673,plain,
    ( m1_subset_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))))) = iProver_top
    | v1_funct_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_37669,c_15727])).

cnf(c_16841,plain,
    ( ~ sP2(sK5(sK7,X0_58,X1_58),X1_58,X0_58,sK7)
    | r3_tsep_1(sK7,X0_58,X1_58)
    | ~ r1_tsep_1(X0_58,X1_58)
    | ~ m1_pre_topc(X0_58,sK7)
    | ~ m1_pre_topc(X1_58,sK7)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_14271])).

cnf(c_17039,plain,
    ( ~ sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7)
    | r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ m1_pre_topc(sK8,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v2_struct_0(sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_16841])).

cnf(c_17040,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7) != iProver_top
    | r3_tsep_1(sK7,sK8,sK9) = iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top
    | m1_pre_topc(sK8,sK7) != iProver_top
    | m1_pre_topc(sK9,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17039])).

cnf(c_17566,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7)
    | v1_funct_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_14276])).

cnf(c_17573,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7) = iProver_top
    | v1_funct_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17566])).

cnf(c_17564,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7)
    | m1_subset_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))))) ),
    inference(instantiation,[status(thm)],[c_14278])).

cnf(c_17577,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7) = iProver_top
    | m1_subset_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17564])).

cnf(c_40923,plain,
    ( m1_subset_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_37673,c_84,c_85,c_86,c_87,c_88,c_89,c_90,c_95,c_96,c_97,c_2566,c_2579,c_2592,c_2605,c_2618,c_2631,c_2644,c_2657,c_2670,c_2683,c_2696,c_2709,c_3366,c_14252,c_17040,c_17573,c_17577,c_18979,c_23361,c_24721])).

cnf(c_29,plain,
    ( sP2(X0,X1,X2,X3)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),k1_tsep_1(X3,X2,X1),X0)
    | ~ v1_funct_2(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_14287,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58)
    | ~ v5_pre_topc(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),k1_tsep_1(X3_58,X2_58,X1_58)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58)
    | ~ v1_funct_2(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58))
    | ~ m1_subset_1(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),k1_tsep_1(X3_58,X2_58,X1_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58))))
    | ~ v1_funct_1(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),k1_tsep_1(X3_58,X2_58,X1_58))) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_15752,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v5_pre_topc(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),k1_tsep_1(X3_58,X2_58,X1_58)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
    | v1_funct_2(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),k1_tsep_1(X3_58,X2_58,X1_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),k1_tsep_1(X3_58,X2_58,X1_58))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14287])).

cnf(c_20784,plain,
    ( sP2(X0_58,sK9,sK8,sK7) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,sK4(X0_58,sK9,sK8,sK7),k1_tsep_1(sK7,sK8,sK9)),k1_tsep_1(sK7,sK8,sK9),X0_58) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,sK4(X0_58,sK9,sK8,sK7),k1_tsep_1(sK7,sK8,sK9)),u1_struct_0(k1_tsep_1(sK7,sK8,sK9)),u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK7,X0_58,sK4(X0_58,sK9,sK8,sK7),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,sK4(X0_58,sK9,sK8,sK7),k1_tsep_1(sK7,sK8,sK9))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14252,c_15752])).

cnf(c_20791,plain,
    ( sP2(X0_58,sK9,sK8,sK7) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,X0_58,sK4(X0_58,sK9,sK8,sK7),sK7),sK7,X0_58) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,X0_58,sK4(X0_58,sK9,sK8,sK7),sK7),u1_struct_0(sK7),u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK7,X0_58,sK4(X0_58,sK9,sK8,sK7),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,X0_58,sK4(X0_58,sK9,sK8,sK7),sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20784,c_14252])).

cnf(c_40947,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7),sK7,sK5(sK7,sK8,sK9)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7),u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_40923,c_20791])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_14311,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
    | ~ v1_funct_1(X0_59)
    | v1_funct_1(k2_partfun1(X0_60,X1_60,X0_59,X2_60)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_15728,plain,
    ( m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k2_partfun1(X0_60,X1_60,X0_59,X2_60)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14311])).

cnf(c_18339,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_1(sK4(X0_58,X1_58,X2_58,X3_58)) != iProver_top
    | v1_funct_1(k2_partfun1(u1_struct_0(X3_58),u1_struct_0(X0_58),sK4(X0_58,X1_58,X2_58,X3_58),X0_60)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15761,c_15728])).

cnf(c_14445,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_1(sK4(X0_58,X1_58,X2_58,X3_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14276])).

cnf(c_28365,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_1(k2_partfun1(u1_struct_0(X3_58),u1_struct_0(X0_58),sK4(X0_58,X1_58,X2_58,X3_58),X0_60)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18339,c_14445])).

cnf(c_37678,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7) = iProver_top
    | v1_funct_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_37669,c_28365])).

cnf(c_41279,plain,
    ( v1_funct_2(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7),u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7),sK7,sK5(sK7,sK8,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_40947,c_84,c_85,c_86,c_87,c_88,c_89,c_90,c_95,c_96,c_97,c_2566,c_2579,c_2592,c_2605,c_2618,c_2631,c_2644,c_2657,c_2670,c_2683,c_2696,c_2709,c_3366,c_14252,c_17040,c_18979,c_23361,c_24721,c_37678])).

cnf(c_41280,plain,
    ( v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7),sK7,sK5(sK7,sK8,sK9)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7),u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))) != iProver_top ),
    inference(renaming,[status(thm)],[c_41279])).

cnf(c_42172,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8),sK8,sK5(sK7,sK8,sK9)) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK9),sK9,sK5(sK7,sK8,sK9)) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7),sK7,sK5(sK7,sK8,sK9)) != iProver_top
    | v1_funct_2(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))) != iProver_top
    | m1_subset_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))))) != iProver_top
    | l1_pre_topc(sK5(sK7,sK8,sK9)) != iProver_top
    | v1_funct_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_42156,c_41280])).

cnf(c_42697,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42172,c_84,c_85,c_86,c_87,c_88,c_89,c_90,c_95,c_96,c_97,c_2566,c_2579,c_2592,c_2605,c_2618,c_2631,c_2644,c_2657,c_2670,c_2683,c_2696,c_2709,c_3366,c_14252,c_17040,c_18979,c_23361,c_24721])).

cnf(c_42706,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X0_60) = k7_relat_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X0_60) ),
    inference(superposition,[status(thm)],[c_28405,c_42697])).

cnf(c_36661,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(X0_58),sK4(X0_58,X1_58,X2_58,sK7),u1_struct_0(sK9)) = k2_tmap_1(sK7,X0_58,sK4(X0_58,X1_58,X2_58,sK7),sK9)
    | sP2(X0_58,X1_58,X2_58,sK7) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_15787,c_36657])).

cnf(c_36804,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | sP2(X0_58,X1_58,X2_58,sK7) = iProver_top
    | k2_partfun1(u1_struct_0(sK7),u1_struct_0(X0_58),sK4(X0_58,X1_58,X2_58,sK7),u1_struct_0(sK9)) = k2_tmap_1(sK7,X0_58,sK4(X0_58,X1_58,X2_58,sK7),sK9)
    | v2_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_36661,c_84,c_85,c_86])).

cnf(c_36805,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(X0_58),sK4(X0_58,X1_58,X2_58,sK7),u1_struct_0(sK9)) = k2_tmap_1(sK7,X0_58,sK4(X0_58,X1_58,X2_58,sK7),sK9)
    | sP2(X0_58,X1_58,X2_58,sK7) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_36804])).

cnf(c_36815,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,X0_58,X1_58)),sK4(sK5(sK7,X0_58,X1_58),X1_58,X0_58,sK7),u1_struct_0(sK9)) = k2_tmap_1(sK7,sK5(sK7,X0_58,X1_58),sK4(sK5(sK7,X0_58,X1_58),X1_58,X0_58,sK7),sK9)
    | r3_tsep_1(sK7,X0_58,X1_58) = iProver_top
    | r1_tsep_1(X0_58,X1_58) != iProver_top
    | m1_pre_topc(X0_58,sK7) != iProver_top
    | m1_pre_topc(X1_58,sK7) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(sK5(sK7,X0_58,X1_58)) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(sK5(sK7,X0_58,X1_58)) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK5(sK7,X0_58,X1_58)) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_36805,c_15768])).

cnf(c_36883,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,X0_58,X1_58)),sK4(sK5(sK7,X0_58,X1_58),X1_58,X0_58,sK7),u1_struct_0(sK9)) = k2_tmap_1(sK7,sK5(sK7,X0_58,X1_58),sK4(sK5(sK7,X0_58,X1_58),X1_58,X0_58,sK7),sK9)
    | r3_tsep_1(sK7,X0_58,X1_58) = iProver_top
    | r1_tsep_1(X0_58,X1_58) != iProver_top
    | m1_pre_topc(X0_58,sK7) != iProver_top
    | m1_pre_topc(X1_58,sK7) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_36815,c_84,c_85,c_86,c_16806,c_16816,c_16826])).

cnf(c_36896,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK9)) = k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK9)
    | r1_tsep_1(sK8,sK9) != iProver_top
    | m1_pre_topc(sK8,sK7) != iProver_top
    | m1_pre_topc(sK9,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_36883,c_28442])).

cnf(c_37009,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9)),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK9)) = k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_36896,c_84,c_85,c_86,c_87,c_88,c_89,c_90,c_3366])).

cnf(c_42755,plain,
    ( k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK9) = k7_relat_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK9)) ),
    inference(demodulation,[status(thm)],[c_42706,c_37009])).

cnf(c_67,plain,
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
    inference(cnf_transformation,[],[f129])).

cnf(c_14254,plain,
    ( ~ sP3(X0_58,X1_58,X2_58,X3_58)
    | v5_pre_topc(X0_59,X1_58,X0_58)
    | ~ v5_pre_topc(k2_tmap_1(X1_58,X0_58,X0_59,X2_58),X2_58,X0_58)
    | ~ v5_pre_topc(k2_tmap_1(X1_58,X0_58,X0_59,X3_58),X3_58,X0_58)
    | ~ v1_funct_2(X0_59,u1_struct_0(X1_58),u1_struct_0(X0_58))
    | ~ v1_funct_2(k2_tmap_1(X1_58,X0_58,X0_59,X2_58),u1_struct_0(X2_58),u1_struct_0(X0_58))
    | ~ v1_funct_2(k2_tmap_1(X1_58,X0_58,X0_59,X3_58),u1_struct_0(X3_58),u1_struct_0(X0_58))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58))))
    | ~ m1_subset_1(k2_tmap_1(X1_58,X0_58,X0_59,X2_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58))))
    | ~ m1_subset_1(k2_tmap_1(X1_58,X0_58,X0_59,X3_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X0_58))))
    | ~ v1_funct_1(X0_59)
    | ~ v1_funct_1(k2_tmap_1(X1_58,X0_58,X0_59,X2_58))
    | ~ v1_funct_1(k2_tmap_1(X1_58,X0_58,X0_59,X3_58)) ),
    inference(subtyping,[status(esa)],[c_67])).

cnf(c_15785,plain,
    ( sP3(X0_58,X1_58,X2_58,X3_58) != iProver_top
    | v5_pre_topc(X0_59,X1_58,X0_58) = iProver_top
    | v5_pre_topc(k2_tmap_1(X1_58,X0_58,X0_59,X2_58),X2_58,X0_58) != iProver_top
    | v5_pre_topc(k2_tmap_1(X1_58,X0_58,X0_59,X3_58),X3_58,X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(X1_58,X0_58,X0_59,X2_58),u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(X1_58,X0_58,X0_59,X3_58),u1_struct_0(X3_58),u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X1_58,X0_58,X0_59,X2_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X1_58,X0_58,X0_59,X3_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k2_tmap_1(X1_58,X0_58,X0_59,X2_58)) != iProver_top
    | v1_funct_1(k2_tmap_1(X1_58,X0_58,X0_59,X3_58)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14254])).

cnf(c_44685,plain,
    ( sP3(sK5(sK7,sK8,sK9),sK7,sK9,X0_58) != iProver_top
    | v5_pre_topc(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7,sK5(sK7,sK8,sK9)) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X0_58),X0_58,sK5(sK7,sK8,sK9)) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK9),sK9,sK5(sK7,sK8,sK9)) != iProver_top
    | v1_funct_2(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X0_58),u1_struct_0(X0_58),u1_struct_0(sK5(sK7,sK8,sK9))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK9),u1_struct_0(sK9),u1_struct_0(sK5(sK7,sK8,sK9))) != iProver_top
    | m1_subset_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK5(sK7,sK8,sK9))))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK7,sK8,sK9))))) != iProver_top
    | v1_funct_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X0_58)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_42755,c_15785])).

cnf(c_44921,plain,
    ( sP3(sK5(sK7,sK8,sK9),sK7,sK9,X0_58) != iProver_top
    | v5_pre_topc(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7,sK5(sK7,sK8,sK9)) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X0_58),X0_58,sK5(sK7,sK8,sK9)) != iProver_top
    | v5_pre_topc(k7_relat_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK9)),sK9,sK5(sK7,sK8,sK9)) != iProver_top
    | v1_funct_2(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X0_58),u1_struct_0(X0_58),u1_struct_0(sK5(sK7,sK8,sK9))) != iProver_top
    | v1_funct_2(k7_relat_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK9)),u1_struct_0(sK9),u1_struct_0(sK5(sK7,sK8,sK9))) != iProver_top
    | m1_subset_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK5(sK7,sK8,sK9))))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK7,sK8,sK9))))) != iProver_top
    | v1_funct_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),X0_58)) != iProver_top
    | v1_funct_1(k7_relat_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK9))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_44685,c_42755])).

cnf(c_44961,plain,
    ( sP3(sK5(sK7,sK8,sK9),sK7,sK9,sK8) != iProver_top
    | v5_pre_topc(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7,sK5(sK7,sK8,sK9)) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8),sK8,sK5(sK7,sK8,sK9)) != iProver_top
    | v5_pre_topc(k7_relat_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK9)),sK9,sK5(sK7,sK8,sK9)) != iProver_top
    | v1_funct_2(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8),u1_struct_0(sK8),u1_struct_0(sK5(sK7,sK8,sK9))) != iProver_top
    | v1_funct_2(k7_relat_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK9)),u1_struct_0(sK9),u1_struct_0(sK5(sK7,sK8,sK9))) != iProver_top
    | m1_subset_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK5(sK7,sK8,sK9))))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK7,sK8,sK9))))) != iProver_top
    | v1_funct_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8)) != iProver_top
    | v1_funct_1(k7_relat_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK9))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_44921])).

cnf(c_33,plain,
    ( sP2(X0,X1,X2,X3)
    | v1_funct_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_14283,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58)
    | v1_funct_1(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),X1_58)) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_15756,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_1(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),X1_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14283])).

cnf(c_44691,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7) = iProver_top
    | v1_funct_1(k7_relat_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK9))) = iProver_top ),
    inference(superposition,[status(thm)],[c_42755,c_15756])).

cnf(c_31,plain,
    ( sP2(X0,X1,X2,X3)
    | v5_pre_topc(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1),X1,X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_14285,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58)
    | v5_pre_topc(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),X1_58),X1_58,X0_58) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_15754,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v5_pre_topc(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),X1_58),X1_58,X0_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14285])).

cnf(c_44690,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7) = iProver_top
    | v5_pre_topc(k7_relat_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK9)),sK9,sK5(sK7,sK8,sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_42755,c_15754])).

cnf(c_32,plain,
    ( sP2(X0,X1,X2,X3)
    | v1_funct_2(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1),u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_14284,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58)
    | v1_funct_2(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),X1_58),u1_struct_0(X1_58),u1_struct_0(X0_58)) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_15755,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_2(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),X1_58),u1_struct_0(X1_58),u1_struct_0(X0_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14284])).

cnf(c_44689,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7) = iProver_top
    | v1_funct_2(k7_relat_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK9)),u1_struct_0(sK9),u1_struct_0(sK5(sK7,sK8,sK9))) = iProver_top ),
    inference(superposition,[status(thm)],[c_42755,c_15755])).

cnf(c_30,plain,
    ( sP2(X0,X1,X2,X3)
    | m1_subset_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_14286,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58)
    | m1_subset_1(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),X1_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_15753,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | m1_subset_1(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),X1_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14286])).

cnf(c_44688,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7) = iProver_top
    | m1_subset_1(k7_relat_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK7,sK8,sK9))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_42755,c_15753])).

cnf(c_10,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(k2_tmap_1(X1,X2,X0,X3),X3,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_14305,plain,
    ( ~ v5_pre_topc(X0_59,X0_58,X1_58)
    | v5_pre_topc(k2_tmap_1(X0_58,X1_58,X0_59,X2_58),X2_58,X1_58)
    | ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ m1_pre_topc(X2_58,X0_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(X0_58)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X0_58)
    | ~ v1_funct_1(X0_59) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_15734,plain,
    ( v5_pre_topc(X0_59,X0_58,X1_58) != iProver_top
    | v5_pre_topc(k2_tmap_1(X0_58,X1_58,X0_59,X2_58),X2_58,X1_58) = iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14305])).

cnf(c_18341,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v5_pre_topc(sK4(X0_58,X1_58,X2_58,X3_58),X3_58,X0_58) != iProver_top
    | v5_pre_topc(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),X4_58),X4_58,X0_58) = iProver_top
    | v1_funct_2(sK4(X0_58,X1_58,X2_58,X3_58),u1_struct_0(X3_58),u1_struct_0(X0_58)) != iProver_top
    | m1_pre_topc(X4_58,X3_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X4_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | v1_funct_1(sK4(X0_58,X1_58,X2_58,X3_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15761,c_15734])).

cnf(c_14444,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_2(sK4(X0_58,X1_58,X2_58,X3_58),u1_struct_0(X3_58),u1_struct_0(X0_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14277])).

cnf(c_35783,plain,
    ( l1_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X4_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | m1_pre_topc(X4_58,X3_58) != iProver_top
    | sP2(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v5_pre_topc(sK4(X0_58,X1_58,X2_58,X3_58),X3_58,X0_58) != iProver_top
    | v5_pre_topc(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),X4_58),X4_58,X0_58) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18341,c_14444,c_14445])).

cnf(c_35784,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v5_pre_topc(sK4(X0_58,X1_58,X2_58,X3_58),X3_58,X0_58) != iProver_top
    | v5_pre_topc(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),X4_58),X4_58,X0_58) = iProver_top
    | m1_pre_topc(X4_58,X3_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X4_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_35783])).

cnf(c_41285,plain,
    ( v5_pre_topc(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7,sK5(sK7,sK8,sK9)) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7),sK7,sK5(sK7,sK8,sK9)) != iProver_top
    | v1_funct_2(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))) != iProver_top
    | m1_subset_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))))) != iProver_top
    | m1_pre_topc(sK7,sK7) != iProver_top
    | v2_struct_0(sK5(sK7,sK8,sK9)) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(sK5(sK7,sK8,sK9)) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK5(sK7,sK8,sK9)) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v1_funct_1(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15735,c_41280])).

cnf(c_17024,plain,
    ( r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ m1_pre_topc(sK8,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | ~ v2_struct_0(sK5(sK7,sK8,sK9))
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v2_struct_0(sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_16805])).

cnf(c_17025,plain,
    ( r3_tsep_1(sK7,sK8,sK9) = iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top
    | m1_pre_topc(sK8,sK7) != iProver_top
    | m1_pre_topc(sK9,sK7) != iProver_top
    | v2_struct_0(sK5(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17024])).

cnf(c_17027,plain,
    ( r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ m1_pre_topc(sK8,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v2_struct_0(sK7)
    | v2_pre_topc(sK5(sK7,sK8,sK9))
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_16815])).

cnf(c_17028,plain,
    ( r3_tsep_1(sK7,sK8,sK9) = iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top
    | m1_pre_topc(sK8,sK7) != iProver_top
    | m1_pre_topc(sK9,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(sK5(sK7,sK8,sK9)) = iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17027])).

cnf(c_17030,plain,
    ( r3_tsep_1(sK7,sK8,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ m1_pre_topc(sK8,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v2_struct_0(sK7)
    | ~ v2_pre_topc(sK7)
    | l1_pre_topc(sK5(sK7,sK8,sK9))
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_16825])).

cnf(c_17031,plain,
    ( r3_tsep_1(sK7,sK8,sK9) = iProver_top
    | r1_tsep_1(sK8,sK9) != iProver_top
    | m1_pre_topc(sK8,sK7) != iProver_top
    | m1_pre_topc(sK9,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK5(sK7,sK8,sK9)) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17030])).

cnf(c_17565,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7)
    | v1_funct_2(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_14277])).

cnf(c_17575,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7) = iProver_top
    | v1_funct_2(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),u1_struct_0(sK7),u1_struct_0(sK5(sK7,sK8,sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17565])).

cnf(c_41409,plain,
    ( v5_pre_topc(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7,sK5(sK7,sK8,sK9)) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7),sK7,sK5(sK7,sK8,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_41285,c_84,c_85,c_86,c_87,c_88,c_89,c_90,c_95,c_96,c_97,c_2566,c_2579,c_2592,c_2605,c_2618,c_2631,c_2644,c_2657,c_2670,c_2683,c_2696,c_2709,c_3366,c_14252,c_16958,c_17025,c_17028,c_17031,c_17040,c_17573,c_17575,c_17577,c_18979,c_23361,c_24721])).

cnf(c_41415,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7) = iProver_top
    | v5_pre_topc(sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK7,sK5(sK7,sK8,sK9)) != iProver_top
    | m1_pre_topc(sK7,sK7) != iProver_top
    | v2_struct_0(sK5(sK7,sK8,sK9)) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(sK5(sK7,sK8,sK9)) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK5(sK7,sK8,sK9)) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_35784,c_41409])).

cnf(c_34,plain,
    ( sP2(X0,X1,X2,X3)
    | m1_subset_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_14282,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58)
    | m1_subset_1(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),X2_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_17559,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7)
    | m1_subset_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK5(sK7,sK8,sK9))))) ),
    inference(instantiation,[status(thm)],[c_14282])).

cnf(c_17587,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7) = iProver_top
    | m1_subset_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK5(sK7,sK8,sK9))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17559])).

cnf(c_35,plain,
    ( sP2(X0,X1,X2,X3)
    | v5_pre_topc(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2),X2,X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_14281,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58)
    | v5_pre_topc(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),X2_58),X2_58,X0_58) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_17560,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7)
    | v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8),sK8,sK5(sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_14281])).

cnf(c_17585,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8),sK8,sK5(sK7,sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17560])).

cnf(c_36,plain,
    ( sP2(X0,X1,X2,X3)
    | v1_funct_2(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_14280,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58)
    | v1_funct_2(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),X2_58),u1_struct_0(X2_58),u1_struct_0(X0_58)) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_17561,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7)
    | v1_funct_2(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8),u1_struct_0(sK8),u1_struct_0(sK5(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_14280])).

cnf(c_17583,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7) = iProver_top
    | v1_funct_2(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8),u1_struct_0(sK8),u1_struct_0(sK5(sK7,sK8,sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17561])).

cnf(c_37,plain,
    ( sP2(X0,X1,X2,X3)
    | v1_funct_1(k2_tmap_1(X3,X0,sK4(X0,X1,X2,X3),X2)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_14279,plain,
    ( sP2(X0_58,X1_58,X2_58,X3_58)
    | v1_funct_1(k2_tmap_1(X3_58,X0_58,sK4(X0_58,X1_58,X2_58,X3_58),X2_58)) ),
    inference(subtyping,[status(esa)],[c_37])).

cnf(c_17563,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7)
    | v1_funct_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8)) ),
    inference(instantiation,[status(thm)],[c_14279])).

cnf(c_17579,plain,
    ( sP2(sK5(sK7,sK8,sK9),sK9,sK8,sK7) = iProver_top
    | v1_funct_1(k2_tmap_1(sK7,sK5(sK7,sK8,sK9),sK4(sK5(sK7,sK8,sK9),sK9,sK8,sK7),sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17563])).

cnf(c_74,negated_conjecture,
    ( sP3(X0,sK7,sK9,sK8)
    | r3_tsep_1(sK7,sK8,sK9)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_14253,negated_conjecture,
    ( sP3(X0_58,sK7,sK9,sK8)
    | r3_tsep_1(sK7,sK8,sK9)
    | v2_struct_0(X0_58)
    | ~ v2_pre_topc(X0_58)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_74])).

cnf(c_17508,plain,
    ( sP3(sK5(sK7,sK8,sK9),sK7,sK9,sK8)
    | r3_tsep_1(sK7,sK8,sK9)
    | v2_struct_0(sK5(sK7,sK8,sK9))
    | ~ v2_pre_topc(sK5(sK7,sK8,sK9))
    | ~ l1_pre_topc(sK5(sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_14253])).

cnf(c_17509,plain,
    ( sP3(sK5(sK7,sK8,sK9),sK7,sK9,sK8) = iProver_top
    | r3_tsep_1(sK7,sK8,sK9) = iProver_top
    | v2_struct_0(sK5(sK7,sK8,sK9)) = iProver_top
    | v2_pre_topc(sK5(sK7,sK8,sK9)) != iProver_top
    | l1_pre_topc(sK5(sK7,sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17508])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44961,c_44691,c_44690,c_44689,c_44688,c_41415,c_28442,c_17587,c_17585,c_17583,c_17579,c_17577,c_17575,c_17573,c_17509,c_17040,c_17031,c_17028,c_17025,c_16958,c_3366,c_90,c_89,c_88,c_87,c_86,c_85,c_84])).


%------------------------------------------------------------------------------
