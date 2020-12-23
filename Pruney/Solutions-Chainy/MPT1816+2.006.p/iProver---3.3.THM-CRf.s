%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:20 EST 2020

% Result     : Theorem 7.48s
% Output     : CNFRefutation 7.48s
% Verified   : 
% Statistics : Number of formulae       :  298 (3630 expanded)
%              Number of clauses        :  204 ( 771 expanded)
%              Number of leaves         :   19 (1258 expanded)
%              Depth                    :   26
%              Number of atoms          : 1935 (112494 expanded)
%              Number of equality atoms :  459 (4290 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal clause size      :   78 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34,plain,(
    ! [X1,X3,X4,X0,X2] :
      ( sP0(X1,X3,X4,X0,X2)
    <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
        & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f40,plain,(
    ! [X1,X3,X4,X0,X2] :
      ( ( sP0(X1,X3,X4,X0,X2)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
        | ~ sP0(X1,X3,X4,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f41,plain,(
    ! [X1,X3,X4,X0,X2] :
      ( ( sP0(X1,X3,X4,X0,X2)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
        | ~ sP0(X1,X3,X4,X0,X2) ) ) ),
    inference(flattening,[],[f40])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f12])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & r4_tsep_1(X0,X3,X4)
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & r4_tsep_1(X0,X3,X4)
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,X0,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & r4_tsep_1(X0,X3,X4)
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,X0,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & r4_tsep_1(X0,X3,X4)
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
            | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
            | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
            | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
            | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
            | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
            | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            | ~ v5_pre_topc(X2,X0,X1)
            | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            | ~ v1_funct_1(X2) )
          & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
              & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
              & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
              & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
              & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
              & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
            | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) ) )
          & r4_tsep_1(X0,X3,X4)
          & k1_tsep_1(X0,X3,X4) = X0
          & m1_pre_topc(X4,X0)
          & ~ v2_struct_0(X4) )
     => ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,sK6))
          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          | ~ v5_pre_topc(X2,X0,X1)
          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(X2) )
        & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1)
            & v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,X2,sK6))
            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
          | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(X2,X0,X1)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X2) ) )
        & r4_tsep_1(X0,X3,sK6)
        & k1_tsep_1(X0,X3,sK6) = X0
        & m1_pre_topc(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                | ~ v5_pre_topc(X2,X0,X1)
                | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                | ~ v1_funct_1(X2) )
              & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                  & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                  & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                  & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                  & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                  & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) ) )
              & r4_tsep_1(X0,X3,X4)
              & k1_tsep_1(X0,X3,X4) = X0
              & m1_pre_topc(X4,X0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
              | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
              | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
              | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
              | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
              | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1)
              | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1))
              | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,sK5))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v5_pre_topc(X2,X0,X1)
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
            & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                & m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1)
                & v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1))
                & v1_funct_1(k2_tmap_1(X0,X1,X2,sK5)) )
              | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) ) )
            & r4_tsep_1(X0,sK5,X4)
            & k1_tsep_1(X0,sK5,X4) = X0
            & m1_pre_topc(X4,X0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                    | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                    | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                    | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                    | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                    | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    | ~ v5_pre_topc(X2,X0,X1)
                    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                    | ~ v1_funct_1(X2) )
                  & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                      & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                      & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                      & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                      & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                      & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                    | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v5_pre_topc(X2,X0,X1)
                      & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X2) ) )
                  & r4_tsep_1(X0,X3,X4)
                  & k1_tsep_1(X0,X3,X4) = X0
                  & m1_pre_topc(X4,X0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1)
                  | ~ v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1))
                  | ~ v1_funct_1(k2_tmap_1(X0,X1,sK4,X4))
                  | ~ m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1)
                  | ~ v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1))
                  | ~ v1_funct_1(k2_tmap_1(X0,X1,sK4,X3))
                  | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  | ~ v5_pre_topc(sK4,X0,X1)
                  | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
                  | ~ v1_funct_1(sK4) )
                & ( ( m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                    & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1)
                    & v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1))
                    & v1_funct_1(k2_tmap_1(X0,X1,sK4,X4))
                    & m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1)
                    & v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(k2_tmap_1(X0,X1,sK4,X3)) )
                  | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v5_pre_topc(sK4,X0,X1)
                    & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(sK4) ) )
                & r4_tsep_1(X0,X3,X4)
                & k1_tsep_1(X0,X3,X4) = X0
                & m1_pre_topc(X4,X0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,X0,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & r4_tsep_1(X0,X3,X4)
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                      | ~ v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3)
                      | ~ v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                      | ~ v1_funct_1(k2_tmap_1(X0,sK3,X2,X4))
                      | ~ m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                      | ~ v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3)
                      | ~ v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                      | ~ v1_funct_1(k2_tmap_1(X0,sK3,X2,X3))
                      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
                      | ~ v5_pre_topc(X2,X0,sK3)
                      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
                      | ~ v1_funct_1(X2) )
                    & ( ( m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                        & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3)
                        & v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                        & v1_funct_1(k2_tmap_1(X0,sK3,X2,X4))
                        & m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                        & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3)
                        & v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                        & v1_funct_1(k2_tmap_1(X0,sK3,X2,X3)) )
                      | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
                        & v5_pre_topc(X2,X0,sK3)
                        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
                        & v1_funct_1(X2) ) )
                    & r4_tsep_1(X0,X3,X4)
                    & k1_tsep_1(X0,X3,X4) = X0
                    & m1_pre_topc(X4,X0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X2,X0,X1)
                          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          | ~ v1_funct_1(X2) )
                        & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                          | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) ) )
                        & r4_tsep_1(X0,X3,X4)
                        & k1_tsep_1(X0,X3,X4) = X0
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
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
                      ( ( ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,sK2,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                          & v5_pre_topc(X2,sK2,X1)
                          & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & r4_tsep_1(sK2,X3,X4)
                      & k1_tsep_1(sK2,X3,X4) = sK2
                      & m1_pre_topc(X4,sK2)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4) )
    & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
        & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
        & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
        & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
      | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v5_pre_topc(sK4,sK2,sK3)
        & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(sK4) ) )
    & r4_tsep_1(sK2,sK5,sK6)
    & k1_tsep_1(sK2,sK5,sK6) = sK2
    & m1_pre_topc(sK6,sK2)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f44,f49,f48,f47,f46,f45])).

fof(f92,plain,(
    k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
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
    inference(pure_predicate_removal,[],[f9])).

fof(f26,plain,(
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

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f89,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f91,plain,(
    m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
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
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
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
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
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
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
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
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f85,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f35,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
      <=> sP0(X1,X3,X4,X0,X2) )
      | ~ sP1(X2,X0,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f37,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
          | ~ sP0(X1,X3,X4,X0,X2) )
        & ( sP0(X1,X3,X4,X0,X2)
          | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) )
      | ~ sP1(X2,X0,X4,X3,X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f38,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
          | ~ sP0(X1,X3,X4,X0,X2) )
        & ( sP0(X1,X3,X4,X0,X2)
          | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) )
      | ~ sP1(X2,X0,X4,X3,X1) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( ( ( m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
            & v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
            & v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
            & v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) )
          | ~ sP0(X4,X3,X2,X1,X0) )
        & ( sP0(X4,X3,X2,X1,X0)
          | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
          | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
          | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
          | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f38])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0)
      | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
      | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
      | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
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
                 => ( r4_tsep_1(X0,X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                            & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
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
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
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
    inference(flattening,[],[f30])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X2,X0,X4,X3,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
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
    inference(definition_folding,[],[f31,f35,f34])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X2,X0,X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ r4_tsep_1(X0,X2,X3)
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
    inference(cnf_transformation,[],[f36])).

fof(f93,plain,(
    r4_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f124,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f116,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f120,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f108,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f100,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f104,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f126,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_20,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2407,plain,
    ( ~ sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
    | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),X1_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_30782,plain,
    ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK6),sK6,X0_54) ),
    inference(instantiation,[status(thm)],[c_2407])).

cnf(c_30814,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
    inference(instantiation,[status(thm)],[c_30782])).

cnf(c_21,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2406,plain,
    ( ~ sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
    | v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),u1_struct_0(X1_54),u1_struct_0(X0_54)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_30783,plain,
    ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK6),u1_struct_0(sK6),u1_struct_0(X0_54)) ),
    inference(instantiation,[status(thm)],[c_2406])).

cnf(c_30810,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_30783])).

cnf(c_24,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2403,plain,
    ( ~ sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
    | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),X3_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_30785,plain,
    ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK5),sK5,X0_54) ),
    inference(instantiation,[status(thm)],[c_2403])).

cnf(c_30802,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
    inference(instantiation,[status(thm)],[c_30785])).

cnf(c_25,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2402,plain,
    ( ~ sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
    | v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),u1_struct_0(X3_54),u1_struct_0(X0_54)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_30786,plain,
    ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK5),u1_struct_0(sK5),u1_struct_0(X0_54)) ),
    inference(instantiation,[status(thm)],[c_2402])).

cnf(c_30798,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_30786])).

cnf(c_62,negated_conjecture,
    ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2392,negated_conjecture,
    ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(subtyping,[status(esa)],[c_62])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2414,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X2_54,X1_54)
    | m1_pre_topc(k1_tsep_1(X1_54,X0_54,X2_54),X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_3341,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1_54,X0_54,X2_54),X1_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2414])).

cnf(c_7431,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2392,c_3341])).

cnf(c_75,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_76,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_75])).

cnf(c_73,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_78,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_66,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_85,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66])).

cnf(c_65,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_86,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65])).

cnf(c_64,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_87,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64])).

cnf(c_63,negated_conjecture,
    ( m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_88,plain,
    ( m1_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63])).

cnf(c_7466,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7431,c_76,c_78,c_85,c_86,c_87,c_88])).

cnf(c_67,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2387,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_67])).

cnf(c_3367,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2387])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2415,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X0_54)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(X1_54)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v1_funct_1(X0_55)
    | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_55,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_55,X2_54) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3340,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_55,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_55,X2_54)
    | v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2415])).

cnf(c_6954,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK3,sK4,X0_54)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3367,c_3340])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2418,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_funct_1(X0_55)
    | k2_partfun1(X0_56,X1_56,X0_55,X2_56) = k7_relat_1(X0_55,X2_56) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3337,plain,
    ( k2_partfun1(X0_56,X1_56,X0_55,X2_56) = k7_relat_1(X0_55,X2_56)
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2418])).

cnf(c_5446,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_56) = k7_relat_1(sK4,X0_56)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3367,c_3337])).

cnf(c_69,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3901,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_56) = k7_relat_1(sK4,X0_56) ),
    inference(instantiation,[status(thm)],[c_2418])).

cnf(c_6704,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_56) = k7_relat_1(sK4,X0_56) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5446,c_69,c_67,c_3901])).

cnf(c_6994,plain,
    ( k2_tmap_1(sK2,sK3,sK4,X0_54) = k7_relat_1(sK4,u1_struct_0(X0_54))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6954,c_6704])).

cnf(c_74,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_77,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_74])).

cnf(c_72,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_79,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_72])).

cnf(c_71,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_80,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_70,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_81,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_70])).

cnf(c_82,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_68,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_83,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_68])).

cnf(c_11339,plain,
    ( m1_pre_topc(X0_54,sK2) != iProver_top
    | k2_tmap_1(sK2,sK3,sK4,X0_54) = k7_relat_1(sK4,u1_struct_0(X0_54)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6994,c_76,c_77,c_78,c_79,c_80,c_81,c_82,c_83])).

cnf(c_11340,plain,
    ( k2_tmap_1(sK2,sK3,sK4,X0_54) = k7_relat_1(sK4,u1_struct_0(X0_54))
    | m1_pre_topc(X0_54,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_11339])).

cnf(c_11350,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_7466,c_11340])).

cnf(c_3,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_761,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_3,c_2])).

cnf(c_2377,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_relat_1(X0_55)
    | k7_relat_1(X0_55,X0_56) = X0_55 ),
    inference(subtyping,[status(esa)],[c_761])).

cnf(c_3377,plain,
    ( k7_relat_1(X0_55,X0_56) = X0_55
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | v1_relat_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2377])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2419,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_56,X1_56)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2466,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_56,X1_56)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2419])).

cnf(c_2529,plain,
    ( k7_relat_1(X0_55,X0_56) = X0_55
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | v1_relat_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2377])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2420,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | ~ v1_relat_1(X1_55)
    | v1_relat_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3851,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | v1_relat_1(X0_55)
    | ~ v1_relat_1(k2_zfmisc_1(X0_56,X1_56)) ),
    inference(instantiation,[status(thm)],[c_2420])).

cnf(c_3852,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | v1_relat_1(X0_55) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_56,X1_56)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3851])).

cnf(c_9241,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | k7_relat_1(X0_55,X0_56) = X0_55 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3377,c_2466,c_2529,c_3852])).

cnf(c_9242,plain,
    ( k7_relat_1(X0_55,X0_56) = X0_55
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9241])).

cnf(c_9251,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK4 ),
    inference(superposition,[status(thm)],[c_3367,c_9242])).

cnf(c_11352,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_11350,c_9251])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2412,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | m1_subset_1(k2_tmap_1(X0_54,X1_54,X0_55,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | ~ l1_struct_0(X2_54)
    | ~ l1_struct_0(X1_54)
    | ~ l1_struct_0(X0_54)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3343,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_54,X1_54,X0_55,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) = iProver_top
    | l1_struct_0(X2_54) != iProver_top
    | l1_struct_0(X1_54) != iProver_top
    | l1_struct_0(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2412])).

cnf(c_17,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | sP0(X4,X3,X2,X1,X0)
    | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
    | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
    | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
    | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_27,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ r4_tsep_1(X1,X0,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_61,negated_conjecture,
    ( r4_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_779,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X2)
    | sK5 != X0
    | sK6 != X3
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_61])).

cnf(c_780,plain,
    ( sP1(sK5,sK2,X0,sK6,X1)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK6,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_779])).

cnf(c_784,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | sP1(sK5,sK2,X0,sK6,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_780,c_75,c_74,c_73,c_66,c_65,c_64,c_63])).

cnf(c_785,plain,
    ( sP1(sK5,sK2,X0,sK6,X1)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_784])).

cnf(c_820,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_tsep_1(X3,X4,X1),X0)
    | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))))
    | v2_struct_0(X6)
    | ~ v2_pre_topc(X6)
    | ~ l1_pre_topc(X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)))
    | X5 != X2
    | X6 != X0
    | sK5 != X4
    | sK6 != X1
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_785])).

cnf(c_821,plain,
    ( sP0(X0,sK6,X1,sK2,sK5)
    | ~ v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(unflattening,[status(thm)],[c_820])).

cnf(c_2376,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5)
    | ~ v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_54)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
    | ~ v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
    | ~ m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54))))
    | v2_struct_0(X0_54)
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(subtyping,[status(esa)],[c_821])).

cnf(c_3378,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_54) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2376])).

cnf(c_3701,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3378,c_2392])).

cnf(c_8522,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_struct_0(X0_54) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3343,c_3701])).

cnf(c_5,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2417,plain,
    ( ~ l1_pre_topc(X0_54)
    | l1_struct_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2472,plain,
    ( l1_pre_topc(X0_54) != iProver_top
    | l1_struct_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2417])).

cnf(c_3983,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2417])).

cnf(c_3984,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3983])).

cnf(c_9121,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8522,c_78,c_2472,c_3984])).

cnf(c_17542,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_11352,c_9121])).

cnf(c_17598,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17542,c_11352])).

cnf(c_17713,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17598])).

cnf(c_13,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_949,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
    | m1_subset_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))))
    | v2_struct_0(X6)
    | ~ v2_pre_topc(X6)
    | ~ l1_pre_topc(X6)
    | ~ v1_funct_1(X5)
    | X5 != X2
    | X6 != X0
    | sK5 != X4
    | sK6 != X1
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_785])).

cnf(c_950,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_949])).

cnf(c_2372,plain,
    ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
    | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54))))
    | v2_struct_0(X0_54)
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_950])).

cnf(c_3382,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54)))) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2372])).

cnf(c_3626,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3382,c_2392])).

cnf(c_30,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_2400,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_3355,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2400])).

cnf(c_18,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2409,plain,
    ( sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
    | ~ v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),X1_54,X0_54)
    | ~ v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),X3_54,X0_54)
    | ~ v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),u1_struct_0(X1_54),u1_struct_0(X0_54))
    | ~ v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),u1_struct_0(X3_54),u1_struct_0(X0_54))
    | ~ m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54))))
    | ~ m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X0_54))))
    | ~ v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_55,X1_54))
    | ~ v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_55,X3_54)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_3346,plain,
    ( sP0(X0_54,X1_54,X0_55,X2_54,X3_54) = iProver_top
    | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),X1_54,X0_54) != iProver_top
    | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),X3_54,X0_54) != iProver_top
    | v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),u1_struct_0(X3_54),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_55,X1_54)) != iProver_top
    | v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_55,X3_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2409])).

cnf(c_8821,plain,
    ( sP0(sK3,sK6,sK4,sK2,X0_54) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_54),X0_54,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_54),u1_struct_0(X0_54),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3355,c_3346])).

cnf(c_84,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_67])).

cnf(c_38,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_112,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_34,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_116,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_179,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_181,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_179])).

cnf(c_2391,negated_conjecture,
    ( m1_pre_topc(sK6,sK2) ),
    inference(subtyping,[status(esa)],[c_63])).

cnf(c_3363,plain,
    ( m1_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2391])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2416,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3339,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2416])).

cnf(c_4463,plain,
    ( l1_pre_topc(sK6) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3363,c_3339])).

cnf(c_6173,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4463,c_78])).

cnf(c_3338,plain,
    ( l1_pre_topc(X0_54) != iProver_top
    | l1_struct_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2417])).

cnf(c_6178,plain,
    ( l1_struct_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_6173,c_3338])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2410,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ l1_struct_0(X2_54)
    | ~ l1_struct_0(X1_54)
    | ~ l1_struct_0(X0_54)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k2_tmap_1(X0_54,X1_54,X0_55,X2_54)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3940,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(X0_54)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2410])).

cnf(c_6185,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK6)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3940])).

cnf(c_6186,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6185])).

cnf(c_9702,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3)))) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_54),X0_54,sK3) != iProver_top
    | sP0(sK3,sK6,sK4,sK2,X0_54) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_54),u1_struct_0(X0_54),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8821,c_78,c_81,c_82,c_83,c_84,c_112,c_116,c_181,c_3984,c_6178,c_6186])).

cnf(c_9703,plain,
    ( sP0(sK3,sK6,sK4,sK2,X0_54) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_54),X0_54,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_54),u1_struct_0(X0_54),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9702])).

cnf(c_9717,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | sP0(sK3,sK6,sK4,sK2,sK2) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3626,c_9703])).

cnf(c_15,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_889,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
    | v1_funct_2(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
    | v2_struct_0(X6)
    | ~ v2_pre_topc(X6)
    | ~ l1_pre_topc(X6)
    | ~ v1_funct_1(X5)
    | X5 != X2
    | X6 != X0
    | sK5 != X4
    | sK6 != X1
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_785])).

cnf(c_890,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_889])).

cnf(c_2374,plain,
    ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
    | v2_struct_0(X0_54)
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_890])).

cnf(c_3380,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2374])).

cnf(c_3609,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3380,c_2392])).

cnf(c_3774,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3609])).

cnf(c_14,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_919,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_tsep_1(X3,X4,X1),X0)
    | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
    | v2_struct_0(X6)
    | ~ v2_pre_topc(X6)
    | ~ l1_pre_topc(X6)
    | ~ v1_funct_1(X5)
    | X5 != X2
    | X6 != X0
    | sK5 != X4
    | sK6 != X1
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_785])).

cnf(c_920,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_919])).

cnf(c_2373,plain,
    ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_54)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
    | v2_struct_0(X0_54)
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_920])).

cnf(c_3381,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_54) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2373])).

cnf(c_3592,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3381,c_2392])).

cnf(c_4985,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3367,c_3592])).

cnf(c_7941,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
    | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4985,c_79,c_80,c_81,c_82,c_83])).

cnf(c_7942,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_7941])).

cnf(c_46,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2396,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_46])).

cnf(c_3359,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2396])).

cnf(c_9715,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3359,c_9703])).

cnf(c_54,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_96,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_50,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_100,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_4261,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3940])).

cnf(c_4262,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4261])).

cnf(c_2389,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(subtyping,[status(esa)],[c_65])).

cnf(c_3365,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2389])).

cnf(c_4464,plain,
    ( l1_pre_topc(sK5) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3365,c_3339])).

cnf(c_4780,plain,
    ( ~ l1_pre_topc(sK5)
    | l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2417])).

cnf(c_4781,plain,
    ( l1_pre_topc(sK5) != iProver_top
    | l1_struct_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4780])).

cnf(c_9822,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9715,c_78,c_81,c_82,c_83,c_84,c_96,c_100,c_181,c_3984,c_4262,c_4464,c_4781])).

cnf(c_16,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_859,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
    | v2_struct_0(X6)
    | ~ v2_pre_topc(X6)
    | ~ l1_pre_topc(X6)
    | ~ v1_funct_1(X5)
    | v1_funct_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)))
    | X5 != X2
    | X6 != X0
    | sK5 != X4
    | sK6 != X1
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_785])).

cnf(c_860,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X1)
    | v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(unflattening,[status(thm)],[c_859])).

cnf(c_2375,plain,
    ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
    | v2_struct_0(X0_54)
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(subtyping,[status(esa)],[c_860])).

cnf(c_3379,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2375])).

cnf(c_3575,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3379,c_2392])).

cnf(c_4772,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3367,c_3575])).

cnf(c_7934,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top
    | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4772,c_79,c_80,c_81,c_82,c_83])).

cnf(c_7935,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7934])).

cnf(c_9839,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9822,c_7935])).

cnf(c_10468,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK2) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9717,c_79,c_80,c_81,c_82,c_83,c_84,c_3774,c_7942,c_9822,c_9839])).

cnf(c_3352,plain,
    ( sP0(X0_54,X1_54,X0_55,X2_54,X3_54) != iProver_top
    | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),X3_54,X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2403])).

cnf(c_10478,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_10468,c_3352])).

cnf(c_17496,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11352,c_10478])).

cnf(c_17529,plain,
    ( v5_pre_topc(sK4,sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17496])).

cnf(c_3950,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(X0_54)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2412])).

cnf(c_9059,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK6)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3950])).

cnf(c_28,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_488,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_69,c_68,c_67])).

cnf(c_489,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(renaming,[status(thm)],[c_488])).

cnf(c_2378,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(subtyping,[status(esa)],[c_489])).

cnf(c_3376,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2378])).

cnf(c_8513,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3343,c_3376])).

cnf(c_8961,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8513,c_78,c_81,c_82,c_83,c_84,c_181,c_3984,c_4262,c_4464,c_4781,c_6178,c_6186])).

cnf(c_8962,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8961])).

cnf(c_8963,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8962])).

cnf(c_6179,plain,
    ( l1_struct_0(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6178])).

cnf(c_180,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30814,c_30810,c_30802,c_30798,c_17713,c_17529,c_9059,c_8963,c_6179,c_3983,c_180,c_67,c_68,c_69,c_70,c_71,c_72,c_73])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:29:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.48/1.55  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.48/1.55  
% 7.48/1.55  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.48/1.55  
% 7.48/1.55  ------  iProver source info
% 7.48/1.55  
% 7.48/1.55  git: date: 2020-06-30 10:37:57 +0100
% 7.48/1.55  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.48/1.55  git: non_committed_changes: false
% 7.48/1.55  git: last_make_outside_of_git: false
% 7.48/1.55  
% 7.48/1.55  ------ 
% 7.48/1.55  
% 7.48/1.55  ------ Input Options
% 7.48/1.55  
% 7.48/1.55  --out_options                           all
% 7.48/1.55  --tptp_safe_out                         true
% 7.48/1.55  --problem_path                          ""
% 7.48/1.55  --include_path                          ""
% 7.48/1.55  --clausifier                            res/vclausify_rel
% 7.48/1.55  --clausifier_options                    --mode clausify
% 7.48/1.55  --stdin                                 false
% 7.48/1.55  --stats_out                             all
% 7.48/1.55  
% 7.48/1.55  ------ General Options
% 7.48/1.55  
% 7.48/1.55  --fof                                   false
% 7.48/1.55  --time_out_real                         305.
% 7.48/1.55  --time_out_virtual                      -1.
% 7.48/1.55  --symbol_type_check                     false
% 7.48/1.55  --clausify_out                          false
% 7.48/1.55  --sig_cnt_out                           false
% 7.48/1.55  --trig_cnt_out                          false
% 7.48/1.55  --trig_cnt_out_tolerance                1.
% 7.48/1.55  --trig_cnt_out_sk_spl                   false
% 7.48/1.55  --abstr_cl_out                          false
% 7.48/1.55  
% 7.48/1.55  ------ Global Options
% 7.48/1.55  
% 7.48/1.55  --schedule                              default
% 7.48/1.55  --add_important_lit                     false
% 7.48/1.55  --prop_solver_per_cl                    1000
% 7.48/1.55  --min_unsat_core                        false
% 7.48/1.55  --soft_assumptions                      false
% 7.48/1.55  --soft_lemma_size                       3
% 7.48/1.55  --prop_impl_unit_size                   0
% 7.48/1.55  --prop_impl_unit                        []
% 7.48/1.55  --share_sel_clauses                     true
% 7.48/1.55  --reset_solvers                         false
% 7.48/1.55  --bc_imp_inh                            [conj_cone]
% 7.48/1.55  --conj_cone_tolerance                   3.
% 7.48/1.55  --extra_neg_conj                        none
% 7.48/1.55  --large_theory_mode                     true
% 7.48/1.55  --prolific_symb_bound                   200
% 7.48/1.55  --lt_threshold                          2000
% 7.48/1.55  --clause_weak_htbl                      true
% 7.48/1.55  --gc_record_bc_elim                     false
% 7.48/1.55  
% 7.48/1.55  ------ Preprocessing Options
% 7.48/1.55  
% 7.48/1.55  --preprocessing_flag                    true
% 7.48/1.55  --time_out_prep_mult                    0.1
% 7.48/1.55  --splitting_mode                        input
% 7.48/1.55  --splitting_grd                         true
% 7.48/1.55  --splitting_cvd                         false
% 7.48/1.55  --splitting_cvd_svl                     false
% 7.48/1.55  --splitting_nvd                         32
% 7.48/1.55  --sub_typing                            true
% 7.48/1.55  --prep_gs_sim                           true
% 7.48/1.55  --prep_unflatten                        true
% 7.48/1.55  --prep_res_sim                          true
% 7.48/1.55  --prep_upred                            true
% 7.48/1.55  --prep_sem_filter                       exhaustive
% 7.48/1.55  --prep_sem_filter_out                   false
% 7.48/1.55  --pred_elim                             true
% 7.48/1.55  --res_sim_input                         true
% 7.48/1.55  --eq_ax_congr_red                       true
% 7.48/1.55  --pure_diseq_elim                       true
% 7.48/1.55  --brand_transform                       false
% 7.48/1.55  --non_eq_to_eq                          false
% 7.48/1.55  --prep_def_merge                        true
% 7.48/1.55  --prep_def_merge_prop_impl              false
% 7.48/1.55  --prep_def_merge_mbd                    true
% 7.48/1.55  --prep_def_merge_tr_red                 false
% 7.48/1.55  --prep_def_merge_tr_cl                  false
% 7.48/1.55  --smt_preprocessing                     true
% 7.48/1.55  --smt_ac_axioms                         fast
% 7.48/1.55  --preprocessed_out                      false
% 7.48/1.55  --preprocessed_stats                    false
% 7.48/1.55  
% 7.48/1.55  ------ Abstraction refinement Options
% 7.48/1.55  
% 7.48/1.55  --abstr_ref                             []
% 7.48/1.55  --abstr_ref_prep                        false
% 7.48/1.55  --abstr_ref_until_sat                   false
% 7.48/1.55  --abstr_ref_sig_restrict                funpre
% 7.48/1.55  --abstr_ref_af_restrict_to_split_sk     false
% 7.48/1.55  --abstr_ref_under                       []
% 7.48/1.55  
% 7.48/1.55  ------ SAT Options
% 7.48/1.55  
% 7.48/1.55  --sat_mode                              false
% 7.48/1.55  --sat_fm_restart_options                ""
% 7.48/1.55  --sat_gr_def                            false
% 7.48/1.55  --sat_epr_types                         true
% 7.48/1.55  --sat_non_cyclic_types                  false
% 7.48/1.55  --sat_finite_models                     false
% 7.48/1.55  --sat_fm_lemmas                         false
% 7.48/1.55  --sat_fm_prep                           false
% 7.48/1.55  --sat_fm_uc_incr                        true
% 7.48/1.55  --sat_out_model                         small
% 7.48/1.55  --sat_out_clauses                       false
% 7.48/1.55  
% 7.48/1.55  ------ QBF Options
% 7.48/1.55  
% 7.48/1.55  --qbf_mode                              false
% 7.48/1.55  --qbf_elim_univ                         false
% 7.48/1.55  --qbf_dom_inst                          none
% 7.48/1.55  --qbf_dom_pre_inst                      false
% 7.48/1.55  --qbf_sk_in                             false
% 7.48/1.55  --qbf_pred_elim                         true
% 7.48/1.55  --qbf_split                             512
% 7.48/1.55  
% 7.48/1.55  ------ BMC1 Options
% 7.48/1.55  
% 7.48/1.55  --bmc1_incremental                      false
% 7.48/1.55  --bmc1_axioms                           reachable_all
% 7.48/1.55  --bmc1_min_bound                        0
% 7.48/1.55  --bmc1_max_bound                        -1
% 7.48/1.55  --bmc1_max_bound_default                -1
% 7.48/1.55  --bmc1_symbol_reachability              true
% 7.48/1.55  --bmc1_property_lemmas                  false
% 7.48/1.55  --bmc1_k_induction                      false
% 7.48/1.55  --bmc1_non_equiv_states                 false
% 7.48/1.55  --bmc1_deadlock                         false
% 7.48/1.55  --bmc1_ucm                              false
% 7.48/1.55  --bmc1_add_unsat_core                   none
% 7.48/1.55  --bmc1_unsat_core_children              false
% 7.48/1.55  --bmc1_unsat_core_extrapolate_axioms    false
% 7.48/1.55  --bmc1_out_stat                         full
% 7.48/1.55  --bmc1_ground_init                      false
% 7.48/1.55  --bmc1_pre_inst_next_state              false
% 7.48/1.55  --bmc1_pre_inst_state                   false
% 7.48/1.55  --bmc1_pre_inst_reach_state             false
% 7.48/1.55  --bmc1_out_unsat_core                   false
% 7.48/1.55  --bmc1_aig_witness_out                  false
% 7.48/1.55  --bmc1_verbose                          false
% 7.48/1.55  --bmc1_dump_clauses_tptp                false
% 7.48/1.55  --bmc1_dump_unsat_core_tptp             false
% 7.48/1.55  --bmc1_dump_file                        -
% 7.48/1.55  --bmc1_ucm_expand_uc_limit              128
% 7.48/1.55  --bmc1_ucm_n_expand_iterations          6
% 7.48/1.55  --bmc1_ucm_extend_mode                  1
% 7.48/1.55  --bmc1_ucm_init_mode                    2
% 7.48/1.55  --bmc1_ucm_cone_mode                    none
% 7.48/1.55  --bmc1_ucm_reduced_relation_type        0
% 7.48/1.55  --bmc1_ucm_relax_model                  4
% 7.48/1.55  --bmc1_ucm_full_tr_after_sat            true
% 7.48/1.55  --bmc1_ucm_expand_neg_assumptions       false
% 7.48/1.55  --bmc1_ucm_layered_model                none
% 7.48/1.55  --bmc1_ucm_max_lemma_size               10
% 7.48/1.55  
% 7.48/1.55  ------ AIG Options
% 7.48/1.55  
% 7.48/1.55  --aig_mode                              false
% 7.48/1.55  
% 7.48/1.55  ------ Instantiation Options
% 7.48/1.55  
% 7.48/1.55  --instantiation_flag                    true
% 7.48/1.55  --inst_sos_flag                         false
% 7.48/1.55  --inst_sos_phase                        true
% 7.48/1.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.48/1.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.48/1.55  --inst_lit_sel_side                     num_symb
% 7.48/1.55  --inst_solver_per_active                1400
% 7.48/1.55  --inst_solver_calls_frac                1.
% 7.48/1.55  --inst_passive_queue_type               priority_queues
% 7.48/1.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.48/1.55  --inst_passive_queues_freq              [25;2]
% 7.48/1.55  --inst_dismatching                      true
% 7.48/1.55  --inst_eager_unprocessed_to_passive     true
% 7.48/1.55  --inst_prop_sim_given                   true
% 7.48/1.55  --inst_prop_sim_new                     false
% 7.48/1.55  --inst_subs_new                         false
% 7.48/1.55  --inst_eq_res_simp                      false
% 7.48/1.55  --inst_subs_given                       false
% 7.48/1.55  --inst_orphan_elimination               true
% 7.48/1.55  --inst_learning_loop_flag               true
% 7.48/1.55  --inst_learning_start                   3000
% 7.48/1.55  --inst_learning_factor                  2
% 7.48/1.55  --inst_start_prop_sim_after_learn       3
% 7.48/1.55  --inst_sel_renew                        solver
% 7.48/1.55  --inst_lit_activity_flag                true
% 7.48/1.55  --inst_restr_to_given                   false
% 7.48/1.55  --inst_activity_threshold               500
% 7.48/1.55  --inst_out_proof                        true
% 7.48/1.55  
% 7.48/1.55  ------ Resolution Options
% 7.48/1.55  
% 7.48/1.55  --resolution_flag                       true
% 7.48/1.55  --res_lit_sel                           adaptive
% 7.48/1.55  --res_lit_sel_side                      none
% 7.48/1.55  --res_ordering                          kbo
% 7.48/1.55  --res_to_prop_solver                    active
% 7.48/1.55  --res_prop_simpl_new                    false
% 7.48/1.55  --res_prop_simpl_given                  true
% 7.48/1.55  --res_passive_queue_type                priority_queues
% 7.48/1.55  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.48/1.55  --res_passive_queues_freq               [15;5]
% 7.48/1.55  --res_forward_subs                      full
% 7.48/1.55  --res_backward_subs                     full
% 7.48/1.55  --res_forward_subs_resolution           true
% 7.48/1.55  --res_backward_subs_resolution          true
% 7.48/1.55  --res_orphan_elimination                true
% 7.48/1.55  --res_time_limit                        2.
% 7.48/1.55  --res_out_proof                         true
% 7.48/1.55  
% 7.48/1.55  ------ Superposition Options
% 7.48/1.55  
% 7.48/1.55  --superposition_flag                    true
% 7.48/1.55  --sup_passive_queue_type                priority_queues
% 7.48/1.55  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.48/1.55  --sup_passive_queues_freq               [8;1;4]
% 7.48/1.55  --demod_completeness_check              fast
% 7.48/1.55  --demod_use_ground                      true
% 7.48/1.55  --sup_to_prop_solver                    passive
% 7.48/1.55  --sup_prop_simpl_new                    true
% 7.48/1.55  --sup_prop_simpl_given                  true
% 7.48/1.55  --sup_fun_splitting                     false
% 7.48/1.55  --sup_smt_interval                      50000
% 7.48/1.55  
% 7.48/1.55  ------ Superposition Simplification Setup
% 7.48/1.55  
% 7.48/1.55  --sup_indices_passive                   []
% 7.48/1.55  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.55  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.55  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.55  --sup_full_triv                         [TrivRules;PropSubs]
% 7.48/1.55  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.55  --sup_full_bw                           [BwDemod]
% 7.48/1.55  --sup_immed_triv                        [TrivRules]
% 7.48/1.55  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.48/1.55  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.55  --sup_immed_bw_main                     []
% 7.48/1.55  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.48/1.55  --sup_input_triv                        [Unflattening;TrivRules]
% 7.48/1.55  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.55  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.48/1.55  
% 7.48/1.55  ------ Combination Options
% 7.48/1.55  
% 7.48/1.55  --comb_res_mult                         3
% 7.48/1.55  --comb_sup_mult                         2
% 7.48/1.55  --comb_inst_mult                        10
% 7.48/1.55  
% 7.48/1.55  ------ Debug Options
% 7.48/1.55  
% 7.48/1.55  --dbg_backtrace                         false
% 7.48/1.55  --dbg_dump_prop_clauses                 false
% 7.48/1.55  --dbg_dump_prop_clauses_file            -
% 7.48/1.55  --dbg_out_stat                          false
% 7.48/1.55  ------ Parsing...
% 7.48/1.55  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.48/1.55  
% 7.48/1.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.48/1.55  
% 7.48/1.55  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.48/1.55  
% 7.48/1.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.48/1.55  ------ Proving...
% 7.48/1.55  ------ Problem Properties 
% 7.48/1.55  
% 7.48/1.55  
% 7.48/1.55  clauses                                 49
% 7.48/1.55  conjectures                             23
% 7.48/1.55  EPR                                     13
% 7.48/1.55  Horn                                    33
% 7.48/1.55  unary                                   15
% 7.48/1.55  binary                                  17
% 7.48/1.55  lits                                    168
% 7.48/1.55  lits eq                                 4
% 7.48/1.55  fd_pure                                 0
% 7.48/1.55  fd_pseudo                               0
% 7.48/1.55  fd_cond                                 0
% 7.48/1.55  fd_pseudo_cond                          0
% 7.48/1.55  AC symbols                              0
% 7.48/1.55  
% 7.48/1.55  ------ Schedule dynamic 5 is on 
% 7.48/1.55  
% 7.48/1.55  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.48/1.55  
% 7.48/1.55  
% 7.48/1.55  ------ 
% 7.48/1.55  Current options:
% 7.48/1.55  ------ 
% 7.48/1.55  
% 7.48/1.55  ------ Input Options
% 7.48/1.55  
% 7.48/1.55  --out_options                           all
% 7.48/1.55  --tptp_safe_out                         true
% 7.48/1.55  --problem_path                          ""
% 7.48/1.55  --include_path                          ""
% 7.48/1.55  --clausifier                            res/vclausify_rel
% 7.48/1.55  --clausifier_options                    --mode clausify
% 7.48/1.55  --stdin                                 false
% 7.48/1.55  --stats_out                             all
% 7.48/1.55  
% 7.48/1.55  ------ General Options
% 7.48/1.55  
% 7.48/1.55  --fof                                   false
% 7.48/1.55  --time_out_real                         305.
% 7.48/1.55  --time_out_virtual                      -1.
% 7.48/1.55  --symbol_type_check                     false
% 7.48/1.55  --clausify_out                          false
% 7.48/1.55  --sig_cnt_out                           false
% 7.48/1.55  --trig_cnt_out                          false
% 7.48/1.55  --trig_cnt_out_tolerance                1.
% 7.48/1.55  --trig_cnt_out_sk_spl                   false
% 7.48/1.55  --abstr_cl_out                          false
% 7.48/1.55  
% 7.48/1.55  ------ Global Options
% 7.48/1.55  
% 7.48/1.55  --schedule                              default
% 7.48/1.55  --add_important_lit                     false
% 7.48/1.55  --prop_solver_per_cl                    1000
% 7.48/1.55  --min_unsat_core                        false
% 7.48/1.55  --soft_assumptions                      false
% 7.48/1.55  --soft_lemma_size                       3
% 7.48/1.55  --prop_impl_unit_size                   0
% 7.48/1.55  --prop_impl_unit                        []
% 7.48/1.55  --share_sel_clauses                     true
% 7.48/1.55  --reset_solvers                         false
% 7.48/1.55  --bc_imp_inh                            [conj_cone]
% 7.48/1.55  --conj_cone_tolerance                   3.
% 7.48/1.55  --extra_neg_conj                        none
% 7.48/1.55  --large_theory_mode                     true
% 7.48/1.55  --prolific_symb_bound                   200
% 7.48/1.55  --lt_threshold                          2000
% 7.48/1.55  --clause_weak_htbl                      true
% 7.48/1.55  --gc_record_bc_elim                     false
% 7.48/1.55  
% 7.48/1.55  ------ Preprocessing Options
% 7.48/1.55  
% 7.48/1.55  --preprocessing_flag                    true
% 7.48/1.55  --time_out_prep_mult                    0.1
% 7.48/1.55  --splitting_mode                        input
% 7.48/1.55  --splitting_grd                         true
% 7.48/1.55  --splitting_cvd                         false
% 7.48/1.55  --splitting_cvd_svl                     false
% 7.48/1.55  --splitting_nvd                         32
% 7.48/1.55  --sub_typing                            true
% 7.48/1.55  --prep_gs_sim                           true
% 7.48/1.55  --prep_unflatten                        true
% 7.48/1.55  --prep_res_sim                          true
% 7.48/1.55  --prep_upred                            true
% 7.48/1.55  --prep_sem_filter                       exhaustive
% 7.48/1.55  --prep_sem_filter_out                   false
% 7.48/1.55  --pred_elim                             true
% 7.48/1.55  --res_sim_input                         true
% 7.48/1.55  --eq_ax_congr_red                       true
% 7.48/1.55  --pure_diseq_elim                       true
% 7.48/1.55  --brand_transform                       false
% 7.48/1.55  --non_eq_to_eq                          false
% 7.48/1.55  --prep_def_merge                        true
% 7.48/1.55  --prep_def_merge_prop_impl              false
% 7.48/1.55  --prep_def_merge_mbd                    true
% 7.48/1.55  --prep_def_merge_tr_red                 false
% 7.48/1.55  --prep_def_merge_tr_cl                  false
% 7.48/1.55  --smt_preprocessing                     true
% 7.48/1.55  --smt_ac_axioms                         fast
% 7.48/1.55  --preprocessed_out                      false
% 7.48/1.55  --preprocessed_stats                    false
% 7.48/1.55  
% 7.48/1.55  ------ Abstraction refinement Options
% 7.48/1.55  
% 7.48/1.55  --abstr_ref                             []
% 7.48/1.55  --abstr_ref_prep                        false
% 7.48/1.55  --abstr_ref_until_sat                   false
% 7.48/1.55  --abstr_ref_sig_restrict                funpre
% 7.48/1.55  --abstr_ref_af_restrict_to_split_sk     false
% 7.48/1.55  --abstr_ref_under                       []
% 7.48/1.55  
% 7.48/1.55  ------ SAT Options
% 7.48/1.55  
% 7.48/1.55  --sat_mode                              false
% 7.48/1.55  --sat_fm_restart_options                ""
% 7.48/1.55  --sat_gr_def                            false
% 7.48/1.55  --sat_epr_types                         true
% 7.48/1.55  --sat_non_cyclic_types                  false
% 7.48/1.55  --sat_finite_models                     false
% 7.48/1.55  --sat_fm_lemmas                         false
% 7.48/1.55  --sat_fm_prep                           false
% 7.48/1.55  --sat_fm_uc_incr                        true
% 7.48/1.55  --sat_out_model                         small
% 7.48/1.55  --sat_out_clauses                       false
% 7.48/1.55  
% 7.48/1.55  ------ QBF Options
% 7.48/1.55  
% 7.48/1.55  --qbf_mode                              false
% 7.48/1.55  --qbf_elim_univ                         false
% 7.48/1.55  --qbf_dom_inst                          none
% 7.48/1.55  --qbf_dom_pre_inst                      false
% 7.48/1.55  --qbf_sk_in                             false
% 7.48/1.55  --qbf_pred_elim                         true
% 7.48/1.55  --qbf_split                             512
% 7.48/1.55  
% 7.48/1.55  ------ BMC1 Options
% 7.48/1.55  
% 7.48/1.55  --bmc1_incremental                      false
% 7.48/1.55  --bmc1_axioms                           reachable_all
% 7.48/1.55  --bmc1_min_bound                        0
% 7.48/1.55  --bmc1_max_bound                        -1
% 7.48/1.55  --bmc1_max_bound_default                -1
% 7.48/1.55  --bmc1_symbol_reachability              true
% 7.48/1.55  --bmc1_property_lemmas                  false
% 7.48/1.55  --bmc1_k_induction                      false
% 7.48/1.55  --bmc1_non_equiv_states                 false
% 7.48/1.55  --bmc1_deadlock                         false
% 7.48/1.55  --bmc1_ucm                              false
% 7.48/1.55  --bmc1_add_unsat_core                   none
% 7.48/1.55  --bmc1_unsat_core_children              false
% 7.48/1.55  --bmc1_unsat_core_extrapolate_axioms    false
% 7.48/1.55  --bmc1_out_stat                         full
% 7.48/1.55  --bmc1_ground_init                      false
% 7.48/1.55  --bmc1_pre_inst_next_state              false
% 7.48/1.55  --bmc1_pre_inst_state                   false
% 7.48/1.55  --bmc1_pre_inst_reach_state             false
% 7.48/1.55  --bmc1_out_unsat_core                   false
% 7.48/1.55  --bmc1_aig_witness_out                  false
% 7.48/1.55  --bmc1_verbose                          false
% 7.48/1.55  --bmc1_dump_clauses_tptp                false
% 7.48/1.55  --bmc1_dump_unsat_core_tptp             false
% 7.48/1.55  --bmc1_dump_file                        -
% 7.48/1.55  --bmc1_ucm_expand_uc_limit              128
% 7.48/1.55  --bmc1_ucm_n_expand_iterations          6
% 7.48/1.55  --bmc1_ucm_extend_mode                  1
% 7.48/1.55  --bmc1_ucm_init_mode                    2
% 7.48/1.55  --bmc1_ucm_cone_mode                    none
% 7.48/1.55  --bmc1_ucm_reduced_relation_type        0
% 7.48/1.55  --bmc1_ucm_relax_model                  4
% 7.48/1.55  --bmc1_ucm_full_tr_after_sat            true
% 7.48/1.55  --bmc1_ucm_expand_neg_assumptions       false
% 7.48/1.55  --bmc1_ucm_layered_model                none
% 7.48/1.55  --bmc1_ucm_max_lemma_size               10
% 7.48/1.55  
% 7.48/1.55  ------ AIG Options
% 7.48/1.55  
% 7.48/1.55  --aig_mode                              false
% 7.48/1.55  
% 7.48/1.55  ------ Instantiation Options
% 7.48/1.55  
% 7.48/1.55  --instantiation_flag                    true
% 7.48/1.55  --inst_sos_flag                         false
% 7.48/1.55  --inst_sos_phase                        true
% 7.48/1.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.48/1.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.48/1.55  --inst_lit_sel_side                     none
% 7.48/1.55  --inst_solver_per_active                1400
% 7.48/1.55  --inst_solver_calls_frac                1.
% 7.48/1.55  --inst_passive_queue_type               priority_queues
% 7.48/1.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.48/1.55  --inst_passive_queues_freq              [25;2]
% 7.48/1.55  --inst_dismatching                      true
% 7.48/1.55  --inst_eager_unprocessed_to_passive     true
% 7.48/1.55  --inst_prop_sim_given                   true
% 7.48/1.55  --inst_prop_sim_new                     false
% 7.48/1.55  --inst_subs_new                         false
% 7.48/1.55  --inst_eq_res_simp                      false
% 7.48/1.55  --inst_subs_given                       false
% 7.48/1.55  --inst_orphan_elimination               true
% 7.48/1.55  --inst_learning_loop_flag               true
% 7.48/1.55  --inst_learning_start                   3000
% 7.48/1.55  --inst_learning_factor                  2
% 7.48/1.55  --inst_start_prop_sim_after_learn       3
% 7.48/1.55  --inst_sel_renew                        solver
% 7.48/1.55  --inst_lit_activity_flag                true
% 7.48/1.55  --inst_restr_to_given                   false
% 7.48/1.55  --inst_activity_threshold               500
% 7.48/1.55  --inst_out_proof                        true
% 7.48/1.55  
% 7.48/1.55  ------ Resolution Options
% 7.48/1.55  
% 7.48/1.55  --resolution_flag                       false
% 7.48/1.55  --res_lit_sel                           adaptive
% 7.48/1.55  --res_lit_sel_side                      none
% 7.48/1.55  --res_ordering                          kbo
% 7.48/1.55  --res_to_prop_solver                    active
% 7.48/1.55  --res_prop_simpl_new                    false
% 7.48/1.55  --res_prop_simpl_given                  true
% 7.48/1.55  --res_passive_queue_type                priority_queues
% 7.48/1.55  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.48/1.55  --res_passive_queues_freq               [15;5]
% 7.48/1.55  --res_forward_subs                      full
% 7.48/1.55  --res_backward_subs                     full
% 7.48/1.55  --res_forward_subs_resolution           true
% 7.48/1.55  --res_backward_subs_resolution          true
% 7.48/1.55  --res_orphan_elimination                true
% 7.48/1.55  --res_time_limit                        2.
% 7.48/1.55  --res_out_proof                         true
% 7.48/1.55  
% 7.48/1.55  ------ Superposition Options
% 7.48/1.55  
% 7.48/1.55  --superposition_flag                    true
% 7.48/1.55  --sup_passive_queue_type                priority_queues
% 7.48/1.55  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.48/1.55  --sup_passive_queues_freq               [8;1;4]
% 7.48/1.55  --demod_completeness_check              fast
% 7.48/1.55  --demod_use_ground                      true
% 7.48/1.55  --sup_to_prop_solver                    passive
% 7.48/1.55  --sup_prop_simpl_new                    true
% 7.48/1.55  --sup_prop_simpl_given                  true
% 7.48/1.55  --sup_fun_splitting                     false
% 7.48/1.55  --sup_smt_interval                      50000
% 7.48/1.55  
% 7.48/1.55  ------ Superposition Simplification Setup
% 7.48/1.55  
% 7.48/1.55  --sup_indices_passive                   []
% 7.48/1.55  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.55  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.55  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.55  --sup_full_triv                         [TrivRules;PropSubs]
% 7.48/1.55  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.55  --sup_full_bw                           [BwDemod]
% 7.48/1.55  --sup_immed_triv                        [TrivRules]
% 7.48/1.55  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.48/1.55  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.55  --sup_immed_bw_main                     []
% 7.48/1.55  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.48/1.55  --sup_input_triv                        [Unflattening;TrivRules]
% 7.48/1.55  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.55  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.48/1.55  
% 7.48/1.55  ------ Combination Options
% 7.48/1.55  
% 7.48/1.55  --comb_res_mult                         3
% 7.48/1.55  --comb_sup_mult                         2
% 7.48/1.55  --comb_inst_mult                        10
% 7.48/1.55  
% 7.48/1.55  ------ Debug Options
% 7.48/1.55  
% 7.48/1.55  --dbg_backtrace                         false
% 7.48/1.55  --dbg_dump_prop_clauses                 false
% 7.48/1.55  --dbg_dump_prop_clauses_file            -
% 7.48/1.55  --dbg_out_stat                          false
% 7.48/1.55  
% 7.48/1.55  
% 7.48/1.55  
% 7.48/1.55  
% 7.48/1.55  ------ Proving...
% 7.48/1.55  
% 7.48/1.55  
% 7.48/1.55  % SZS status Theorem for theBenchmark.p
% 7.48/1.55  
% 7.48/1.55  % SZS output start CNFRefutation for theBenchmark.p
% 7.48/1.55  
% 7.48/1.55  fof(f34,plain,(
% 7.48/1.55    ! [X1,X3,X4,X0,X2] : (sP0(X1,X3,X4,X0,X2) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))),
% 7.48/1.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.48/1.55  
% 7.48/1.55  fof(f40,plain,(
% 7.48/1.55    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 7.48/1.55    inference(nnf_transformation,[],[f34])).
% 7.48/1.55  
% 7.48/1.55  fof(f41,plain,(
% 7.48/1.55    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 7.48/1.55    inference(flattening,[],[f40])).
% 7.48/1.55  
% 7.48/1.55  fof(f42,plain,(
% 7.48/1.55    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) & ((m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 7.48/1.55    inference(rectify,[],[f41])).
% 7.48/1.55  
% 7.48/1.55  fof(f75,plain,(
% 7.48/1.55    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 7.48/1.55    inference(cnf_transformation,[],[f42])).
% 7.48/1.55  
% 7.48/1.55  fof(f74,plain,(
% 7.48/1.55    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 7.48/1.55    inference(cnf_transformation,[],[f42])).
% 7.48/1.55  
% 7.48/1.55  fof(f71,plain,(
% 7.48/1.55    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 7.48/1.55    inference(cnf_transformation,[],[f42])).
% 7.48/1.55  
% 7.48/1.55  fof(f70,plain,(
% 7.48/1.55    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 7.48/1.55    inference(cnf_transformation,[],[f42])).
% 7.48/1.55  
% 7.48/1.55  fof(f12,conjecture,(
% 7.48/1.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 7.48/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.48/1.55  
% 7.48/1.55  fof(f13,negated_conjecture,(
% 7.48/1.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 7.48/1.55    inference(negated_conjecture,[],[f12])).
% 7.48/1.55  
% 7.48/1.55  fof(f32,plain,(
% 7.48/1.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & (r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0)) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.48/1.55    inference(ennf_transformation,[],[f13])).
% 7.48/1.55  
% 7.48/1.55  fof(f33,plain,(
% 7.48/1.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.48/1.55    inference(flattening,[],[f32])).
% 7.48/1.55  
% 7.48/1.55  fof(f43,plain,(
% 7.48/1.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.48/1.55    inference(nnf_transformation,[],[f33])).
% 7.48/1.55  
% 7.48/1.55  fof(f44,plain,(
% 7.48/1.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.48/1.55    inference(flattening,[],[f43])).
% 7.48/1.55  
% 7.48/1.55  fof(f49,plain,(
% 7.48/1.55    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((~m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,sK6) & k1_tsep_1(X0,X3,sK6) = X0 & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 7.48/1.55    introduced(choice_axiom,[])).
% 7.48/1.55  
% 7.48/1.55  fof(f48,plain,(
% 7.48/1.55    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK5)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK5))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,sK5,X4) & k1_tsep_1(X0,sK5,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 7.48/1.55    introduced(choice_axiom,[])).
% 7.48/1.55  
% 7.48/1.55  fof(f47,plain,(
% 7.48/1.55    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(sK4,X0,X1) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) & m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X3))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK4,X0,X1) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 7.48/1.55    introduced(choice_axiom,[])).
% 7.48/1.55  
% 7.48/1.55  fof(f46,plain,(
% 7.48/1.55    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(X2,X0,sK3) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) & m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v5_pre_topc(X2,X0,sK3) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 7.48/1.55    introduced(choice_axiom,[])).
% 7.48/1.55  
% 7.48/1.55  fof(f45,plain,(
% 7.48/1.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(sK2,X3,X4) & k1_tsep_1(sK2,X3,X4) = sK2 & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 7.48/1.55    introduced(choice_axiom,[])).
% 7.48/1.55  
% 7.48/1.55  fof(f50,plain,(
% 7.48/1.55    (((((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,sK5,sK6) & k1_tsep_1(sK2,sK5,sK6) = sK2 & m1_pre_topc(sK6,sK2) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 7.48/1.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f44,f49,f48,f47,f46,f45])).
% 7.48/1.55  
% 7.48/1.55  fof(f92,plain,(
% 7.48/1.55    k1_tsep_1(sK2,sK5,sK6) = sK2),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  fof(f9,axiom,(
% 7.48/1.55    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 7.48/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.48/1.55  
% 7.48/1.55  fof(f14,plain,(
% 7.48/1.55    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 7.48/1.55    inference(pure_predicate_removal,[],[f9])).
% 7.48/1.55  
% 7.48/1.55  fof(f26,plain,(
% 7.48/1.55    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.48/1.55    inference(ennf_transformation,[],[f14])).
% 7.48/1.55  
% 7.48/1.55  fof(f27,plain,(
% 7.48/1.55    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.48/1.55    inference(flattening,[],[f26])).
% 7.48/1.55  
% 7.48/1.55  fof(f60,plain,(
% 7.48/1.55    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.48/1.55    inference(cnf_transformation,[],[f27])).
% 7.48/1.55  
% 7.48/1.55  fof(f79,plain,(
% 7.48/1.55    ~v2_struct_0(sK2)),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  fof(f81,plain,(
% 7.48/1.55    l1_pre_topc(sK2)),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  fof(f88,plain,(
% 7.48/1.55    ~v2_struct_0(sK5)),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  fof(f89,plain,(
% 7.48/1.55    m1_pre_topc(sK5,sK2)),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  fof(f90,plain,(
% 7.48/1.55    ~v2_struct_0(sK6)),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  fof(f91,plain,(
% 7.48/1.55    m1_pre_topc(sK6,sK2)),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  fof(f87,plain,(
% 7.48/1.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  fof(f8,axiom,(
% 7.48/1.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 7.48/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.48/1.55  
% 7.48/1.55  fof(f24,plain,(
% 7.48/1.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.48/1.55    inference(ennf_transformation,[],[f8])).
% 7.48/1.55  
% 7.48/1.55  fof(f25,plain,(
% 7.48/1.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.48/1.55    inference(flattening,[],[f24])).
% 7.48/1.55  
% 7.48/1.55  fof(f58,plain,(
% 7.48/1.55    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.48/1.55    inference(cnf_transformation,[],[f25])).
% 7.48/1.55  
% 7.48/1.55  fof(f5,axiom,(
% 7.48/1.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.48/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.48/1.55  
% 7.48/1.55  fof(f20,plain,(
% 7.48/1.55    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.48/1.55    inference(ennf_transformation,[],[f5])).
% 7.48/1.55  
% 7.48/1.55  fof(f21,plain,(
% 7.48/1.55    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.48/1.55    inference(flattening,[],[f20])).
% 7.48/1.55  
% 7.48/1.55  fof(f55,plain,(
% 7.48/1.55    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.48/1.55    inference(cnf_transformation,[],[f21])).
% 7.48/1.55  
% 7.48/1.55  fof(f85,plain,(
% 7.48/1.55    v1_funct_1(sK4)),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  fof(f80,plain,(
% 7.48/1.55    v2_pre_topc(sK2)),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  fof(f82,plain,(
% 7.48/1.55    ~v2_struct_0(sK3)),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  fof(f83,plain,(
% 7.48/1.55    v2_pre_topc(sK3)),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  fof(f84,plain,(
% 7.48/1.55    l1_pre_topc(sK3)),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  fof(f86,plain,(
% 7.48/1.55    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  fof(f4,axiom,(
% 7.48/1.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.48/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.48/1.55  
% 7.48/1.55  fof(f15,plain,(
% 7.48/1.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.48/1.55    inference(pure_predicate_removal,[],[f4])).
% 7.48/1.55  
% 7.48/1.55  fof(f19,plain,(
% 7.48/1.55    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.48/1.55    inference(ennf_transformation,[],[f15])).
% 7.48/1.55  
% 7.48/1.55  fof(f54,plain,(
% 7.48/1.55    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.48/1.55    inference(cnf_transformation,[],[f19])).
% 7.48/1.55  
% 7.48/1.55  fof(f3,axiom,(
% 7.48/1.55    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.48/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.48/1.55  
% 7.48/1.55  fof(f17,plain,(
% 7.48/1.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.48/1.55    inference(ennf_transformation,[],[f3])).
% 7.48/1.55  
% 7.48/1.55  fof(f18,plain,(
% 7.48/1.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.48/1.55    inference(flattening,[],[f17])).
% 7.48/1.55  
% 7.48/1.55  fof(f53,plain,(
% 7.48/1.55    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.48/1.55    inference(cnf_transformation,[],[f18])).
% 7.48/1.55  
% 7.48/1.55  fof(f2,axiom,(
% 7.48/1.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.48/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.48/1.55  
% 7.48/1.55  fof(f52,plain,(
% 7.48/1.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.48/1.55    inference(cnf_transformation,[],[f2])).
% 7.48/1.55  
% 7.48/1.55  fof(f1,axiom,(
% 7.48/1.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.48/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.48/1.55  
% 7.48/1.55  fof(f16,plain,(
% 7.48/1.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.48/1.55    inference(ennf_transformation,[],[f1])).
% 7.48/1.55  
% 7.48/1.55  fof(f51,plain,(
% 7.48/1.55    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.48/1.55    inference(cnf_transformation,[],[f16])).
% 7.48/1.55  
% 7.48/1.55  fof(f10,axiom,(
% 7.48/1.55    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 7.48/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.48/1.55  
% 7.48/1.55  fof(f28,plain,(
% 7.48/1.55    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 7.48/1.55    inference(ennf_transformation,[],[f10])).
% 7.48/1.55  
% 7.48/1.55  fof(f29,plain,(
% 7.48/1.55    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 7.48/1.55    inference(flattening,[],[f28])).
% 7.48/1.55  
% 7.48/1.55  fof(f63,plain,(
% 7.48/1.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 7.48/1.55    inference(cnf_transformation,[],[f29])).
% 7.48/1.55  
% 7.48/1.55  fof(f35,plain,(
% 7.48/1.55    ! [X2,X0,X4,X3,X1] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> sP0(X1,X3,X4,X0,X2)) | ~sP1(X2,X0,X4,X3,X1))),
% 7.48/1.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 7.48/1.55  
% 7.48/1.55  fof(f37,plain,(
% 7.48/1.55    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))))) | ~sP1(X2,X0,X4,X3,X1))),
% 7.48/1.55    inference(nnf_transformation,[],[f35])).
% 7.48/1.55  
% 7.48/1.55  fof(f38,plain,(
% 7.48/1.55    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))))) | ~sP1(X2,X0,X4,X3,X1))),
% 7.48/1.55    inference(flattening,[],[f37])).
% 7.48/1.55  
% 7.48/1.55  fof(f39,plain,(
% 7.48/1.55    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) & v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) & v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) & v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))))) | ~sP1(X0,X1,X2,X3,X4))),
% 7.48/1.55    inference(rectify,[],[f38])).
% 7.48/1.55  
% 7.48/1.55  fof(f64,plain,(
% 7.48/1.55    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.48/1.55    inference(cnf_transformation,[],[f39])).
% 7.48/1.55  
% 7.48/1.55  fof(f11,axiom,(
% 7.48/1.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))))))))),
% 7.48/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.48/1.55  
% 7.48/1.55  fof(f30,plain,(
% 7.48/1.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.48/1.55    inference(ennf_transformation,[],[f11])).
% 7.48/1.55  
% 7.48/1.55  fof(f31,plain,(
% 7.48/1.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.48/1.55    inference(flattening,[],[f30])).
% 7.48/1.55  
% 7.48/1.55  fof(f36,plain,(
% 7.48/1.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X2,X0,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.48/1.55    inference(definition_folding,[],[f31,f35,f34])).
% 7.48/1.55  
% 7.48/1.55  fof(f78,plain,(
% 7.48/1.55    ( ! [X4,X2,X0,X3,X1] : (sP1(X2,X0,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.48/1.55    inference(cnf_transformation,[],[f36])).
% 7.48/1.55  
% 7.48/1.55  fof(f93,plain,(
% 7.48/1.55    r4_tsep_1(sK2,sK5,sK6)),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  fof(f6,axiom,(
% 7.48/1.55    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.48/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.48/1.55  
% 7.48/1.55  fof(f22,plain,(
% 7.48/1.55    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.48/1.55    inference(ennf_transformation,[],[f6])).
% 7.48/1.55  
% 7.48/1.55  fof(f56,plain,(
% 7.48/1.55    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.48/1.55    inference(cnf_transformation,[],[f22])).
% 7.48/1.55  
% 7.48/1.55  fof(f68,plain,(
% 7.48/1.55    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.48/1.55    inference(cnf_transformation,[],[f39])).
% 7.48/1.55  
% 7.48/1.55  fof(f124,plain,(
% 7.48/1.55    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  fof(f77,plain,(
% 7.48/1.55    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) )),
% 7.48/1.55    inference(cnf_transformation,[],[f42])).
% 7.48/1.55  
% 7.48/1.55  fof(f116,plain,(
% 7.48/1.55    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  fof(f120,plain,(
% 7.48/1.55    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  fof(f7,axiom,(
% 7.48/1.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.48/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.48/1.55  
% 7.48/1.55  fof(f23,plain,(
% 7.48/1.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.48/1.55    inference(ennf_transformation,[],[f7])).
% 7.48/1.55  
% 7.48/1.55  fof(f57,plain,(
% 7.48/1.55    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.48/1.55    inference(cnf_transformation,[],[f23])).
% 7.48/1.55  
% 7.48/1.55  fof(f61,plain,(
% 7.48/1.55    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 7.48/1.55    inference(cnf_transformation,[],[f29])).
% 7.48/1.55  
% 7.48/1.55  fof(f66,plain,(
% 7.48/1.55    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.48/1.55    inference(cnf_transformation,[],[f39])).
% 7.48/1.55  
% 7.48/1.55  fof(f67,plain,(
% 7.48/1.55    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.48/1.55    inference(cnf_transformation,[],[f39])).
% 7.48/1.55  
% 7.48/1.55  fof(f108,plain,(
% 7.48/1.55    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  fof(f100,plain,(
% 7.48/1.55    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  fof(f104,plain,(
% 7.48/1.55    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  fof(f65,plain,(
% 7.48/1.55    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.48/1.55    inference(cnf_transformation,[],[f39])).
% 7.48/1.55  
% 7.48/1.55  fof(f126,plain,(
% 7.48/1.55    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 7.48/1.55    inference(cnf_transformation,[],[f50])).
% 7.48/1.55  
% 7.48/1.55  cnf(c_20,plain,
% 7.48/1.55      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) ),
% 7.48/1.55      inference(cnf_transformation,[],[f75]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2407,plain,
% 7.48/1.55      ( ~ sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),X1_54,X0_54) ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_20]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_30782,plain,
% 7.48/1.55      ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK6),sK6,X0_54) ),
% 7.48/1.55      inference(instantiation,[status(thm)],[c_2407]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_30814,plain,
% 7.48/1.55      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
% 7.48/1.55      inference(instantiation,[status(thm)],[c_30782]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_21,plain,
% 7.48/1.55      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.48/1.55      | v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) ),
% 7.48/1.55      inference(cnf_transformation,[],[f74]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2406,plain,
% 7.48/1.55      ( ~ sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
% 7.48/1.55      | v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),u1_struct_0(X1_54),u1_struct_0(X0_54)) ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_21]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_30783,plain,
% 7.48/1.55      ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
% 7.48/1.55      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK6),u1_struct_0(sK6),u1_struct_0(X0_54)) ),
% 7.48/1.55      inference(instantiation,[status(thm)],[c_2406]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_30810,plain,
% 7.48/1.55      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 7.48/1.55      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
% 7.48/1.55      inference(instantiation,[status(thm)],[c_30783]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_24,plain,
% 7.48/1.55      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) ),
% 7.48/1.55      inference(cnf_transformation,[],[f71]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2403,plain,
% 7.48/1.55      ( ~ sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),X3_54,X0_54) ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_24]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_30785,plain,
% 7.48/1.55      ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK5),sK5,X0_54) ),
% 7.48/1.55      inference(instantiation,[status(thm)],[c_2403]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_30802,plain,
% 7.48/1.55      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
% 7.48/1.55      inference(instantiation,[status(thm)],[c_30785]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_25,plain,
% 7.48/1.55      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.48/1.55      | v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) ),
% 7.48/1.55      inference(cnf_transformation,[],[f70]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2402,plain,
% 7.48/1.55      ( ~ sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
% 7.48/1.55      | v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),u1_struct_0(X3_54),u1_struct_0(X0_54)) ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_25]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_30786,plain,
% 7.48/1.55      ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
% 7.48/1.55      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK5),u1_struct_0(sK5),u1_struct_0(X0_54)) ),
% 7.48/1.55      inference(instantiation,[status(thm)],[c_2402]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_30798,plain,
% 7.48/1.55      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 7.48/1.55      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 7.48/1.55      inference(instantiation,[status(thm)],[c_30786]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_62,negated_conjecture,
% 7.48/1.55      ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
% 7.48/1.55      inference(cnf_transformation,[],[f92]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2392,negated_conjecture,
% 7.48/1.55      ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_62]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_8,plain,
% 7.48/1.55      ( ~ m1_pre_topc(X0,X1)
% 7.48/1.55      | ~ m1_pre_topc(X2,X1)
% 7.48/1.55      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 7.48/1.55      | v2_struct_0(X1)
% 7.48/1.55      | v2_struct_0(X0)
% 7.48/1.55      | v2_struct_0(X2)
% 7.48/1.55      | ~ l1_pre_topc(X1) ),
% 7.48/1.55      inference(cnf_transformation,[],[f60]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2414,plain,
% 7.48/1.55      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.48/1.55      | ~ m1_pre_topc(X2_54,X1_54)
% 7.48/1.55      | m1_pre_topc(k1_tsep_1(X1_54,X0_54,X2_54),X1_54)
% 7.48/1.55      | v2_struct_0(X0_54)
% 7.48/1.55      | v2_struct_0(X1_54)
% 7.48/1.55      | v2_struct_0(X2_54)
% 7.48/1.55      | ~ l1_pre_topc(X1_54) ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_8]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3341,plain,
% 7.48/1.55      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.48/1.55      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 7.48/1.55      | m1_pre_topc(k1_tsep_1(X1_54,X0_54,X2_54),X1_54) = iProver_top
% 7.48/1.55      | v2_struct_0(X1_54) = iProver_top
% 7.48/1.55      | v2_struct_0(X0_54) = iProver_top
% 7.48/1.55      | v2_struct_0(X2_54) = iProver_top
% 7.48/1.55      | l1_pre_topc(X1_54) != iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_2414]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_7431,plain,
% 7.48/1.55      ( m1_pre_topc(sK5,sK2) != iProver_top
% 7.48/1.55      | m1_pre_topc(sK6,sK2) != iProver_top
% 7.48/1.55      | m1_pre_topc(sK2,sK2) = iProver_top
% 7.48/1.55      | v2_struct_0(sK5) = iProver_top
% 7.48/1.55      | v2_struct_0(sK6) = iProver_top
% 7.48/1.55      | v2_struct_0(sK2) = iProver_top
% 7.48/1.55      | l1_pre_topc(sK2) != iProver_top ),
% 7.48/1.55      inference(superposition,[status(thm)],[c_2392,c_3341]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_75,negated_conjecture,
% 7.48/1.55      ( ~ v2_struct_0(sK2) ),
% 7.48/1.55      inference(cnf_transformation,[],[f79]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_76,plain,
% 7.48/1.55      ( v2_struct_0(sK2) != iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_75]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_73,negated_conjecture,
% 7.48/1.55      ( l1_pre_topc(sK2) ),
% 7.48/1.55      inference(cnf_transformation,[],[f81]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_78,plain,
% 7.48/1.55      ( l1_pre_topc(sK2) = iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_73]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_66,negated_conjecture,
% 7.48/1.55      ( ~ v2_struct_0(sK5) ),
% 7.48/1.55      inference(cnf_transformation,[],[f88]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_85,plain,
% 7.48/1.55      ( v2_struct_0(sK5) != iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_66]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_65,negated_conjecture,
% 7.48/1.55      ( m1_pre_topc(sK5,sK2) ),
% 7.48/1.55      inference(cnf_transformation,[],[f89]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_86,plain,
% 7.48/1.55      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_65]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_64,negated_conjecture,
% 7.48/1.55      ( ~ v2_struct_0(sK6) ),
% 7.48/1.55      inference(cnf_transformation,[],[f90]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_87,plain,
% 7.48/1.55      ( v2_struct_0(sK6) != iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_64]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_63,negated_conjecture,
% 7.48/1.55      ( m1_pre_topc(sK6,sK2) ),
% 7.48/1.55      inference(cnf_transformation,[],[f91]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_88,plain,
% 7.48/1.55      ( m1_pre_topc(sK6,sK2) = iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_63]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_7466,plain,
% 7.48/1.55      ( m1_pre_topc(sK2,sK2) = iProver_top ),
% 7.48/1.55      inference(global_propositional_subsumption,
% 7.48/1.55                [status(thm)],
% 7.48/1.55                [c_7431,c_76,c_78,c_85,c_86,c_87,c_88]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_67,negated_conjecture,
% 7.48/1.55      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 7.48/1.55      inference(cnf_transformation,[],[f87]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2387,negated_conjecture,
% 7.48/1.55      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_67]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3367,plain,
% 7.48/1.55      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_2387]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_7,plain,
% 7.48/1.55      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.48/1.55      | ~ m1_pre_topc(X3,X1)
% 7.48/1.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.48/1.55      | v2_struct_0(X1)
% 7.48/1.55      | v2_struct_0(X2)
% 7.48/1.55      | ~ v2_pre_topc(X2)
% 7.48/1.55      | ~ v2_pre_topc(X1)
% 7.48/1.55      | ~ l1_pre_topc(X1)
% 7.48/1.55      | ~ l1_pre_topc(X2)
% 7.48/1.55      | ~ v1_funct_1(X0)
% 7.48/1.55      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 7.48/1.55      inference(cnf_transformation,[],[f58]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2415,plain,
% 7.48/1.55      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.48/1.55      | ~ m1_pre_topc(X2_54,X0_54)
% 7.48/1.55      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.48/1.55      | v2_struct_0(X0_54)
% 7.48/1.55      | v2_struct_0(X1_54)
% 7.48/1.55      | ~ v2_pre_topc(X0_54)
% 7.48/1.55      | ~ v2_pre_topc(X1_54)
% 7.48/1.55      | ~ l1_pre_topc(X0_54)
% 7.48/1.55      | ~ l1_pre_topc(X1_54)
% 7.48/1.55      | ~ v1_funct_1(X0_55)
% 7.48/1.55      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_55,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_55,X2_54) ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_7]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3340,plain,
% 7.48/1.55      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_55,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_55,X2_54)
% 7.48/1.55      | v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.48/1.55      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 7.48/1.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.48/1.55      | v2_struct_0(X1_54) = iProver_top
% 7.48/1.55      | v2_struct_0(X0_54) = iProver_top
% 7.48/1.55      | v2_pre_topc(X1_54) != iProver_top
% 7.48/1.55      | v2_pre_topc(X0_54) != iProver_top
% 7.48/1.55      | l1_pre_topc(X1_54) != iProver_top
% 7.48/1.55      | l1_pre_topc(X0_54) != iProver_top
% 7.48/1.55      | v1_funct_1(X0_55) != iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_2415]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_6954,plain,
% 7.48/1.55      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK3,sK4,X0_54)
% 7.48/1.55      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.48/1.55      | m1_pre_topc(X0_54,sK2) != iProver_top
% 7.48/1.55      | v2_struct_0(sK3) = iProver_top
% 7.48/1.55      | v2_struct_0(sK2) = iProver_top
% 7.48/1.55      | v2_pre_topc(sK3) != iProver_top
% 7.48/1.55      | v2_pre_topc(sK2) != iProver_top
% 7.48/1.55      | l1_pre_topc(sK3) != iProver_top
% 7.48/1.55      | l1_pre_topc(sK2) != iProver_top
% 7.48/1.55      | v1_funct_1(sK4) != iProver_top ),
% 7.48/1.55      inference(superposition,[status(thm)],[c_3367,c_3340]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_4,plain,
% 7.48/1.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.48/1.55      | ~ v1_funct_1(X0)
% 7.48/1.55      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.48/1.55      inference(cnf_transformation,[],[f55]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2418,plain,
% 7.48/1.55      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 7.48/1.55      | ~ v1_funct_1(X0_55)
% 7.48/1.55      | k2_partfun1(X0_56,X1_56,X0_55,X2_56) = k7_relat_1(X0_55,X2_56) ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_4]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3337,plain,
% 7.48/1.55      ( k2_partfun1(X0_56,X1_56,X0_55,X2_56) = k7_relat_1(X0_55,X2_56)
% 7.48/1.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 7.48/1.55      | v1_funct_1(X0_55) != iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_2418]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_5446,plain,
% 7.48/1.55      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_56) = k7_relat_1(sK4,X0_56)
% 7.48/1.55      | v1_funct_1(sK4) != iProver_top ),
% 7.48/1.55      inference(superposition,[status(thm)],[c_3367,c_3337]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_69,negated_conjecture,
% 7.48/1.55      ( v1_funct_1(sK4) ),
% 7.48/1.55      inference(cnf_transformation,[],[f85]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3901,plain,
% 7.48/1.55      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.48/1.55      | ~ v1_funct_1(sK4)
% 7.48/1.55      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_56) = k7_relat_1(sK4,X0_56) ),
% 7.48/1.55      inference(instantiation,[status(thm)],[c_2418]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_6704,plain,
% 7.48/1.55      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_56) = k7_relat_1(sK4,X0_56) ),
% 7.48/1.55      inference(global_propositional_subsumption,
% 7.48/1.55                [status(thm)],
% 7.48/1.55                [c_5446,c_69,c_67,c_3901]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_6994,plain,
% 7.48/1.55      ( k2_tmap_1(sK2,sK3,sK4,X0_54) = k7_relat_1(sK4,u1_struct_0(X0_54))
% 7.48/1.55      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.48/1.55      | m1_pre_topc(X0_54,sK2) != iProver_top
% 7.48/1.55      | v2_struct_0(sK3) = iProver_top
% 7.48/1.55      | v2_struct_0(sK2) = iProver_top
% 7.48/1.55      | v2_pre_topc(sK3) != iProver_top
% 7.48/1.55      | v2_pre_topc(sK2) != iProver_top
% 7.48/1.55      | l1_pre_topc(sK3) != iProver_top
% 7.48/1.55      | l1_pre_topc(sK2) != iProver_top
% 7.48/1.55      | v1_funct_1(sK4) != iProver_top ),
% 7.48/1.55      inference(demodulation,[status(thm)],[c_6954,c_6704]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_74,negated_conjecture,
% 7.48/1.55      ( v2_pre_topc(sK2) ),
% 7.48/1.55      inference(cnf_transformation,[],[f80]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_77,plain,
% 7.48/1.55      ( v2_pre_topc(sK2) = iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_74]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_72,negated_conjecture,
% 7.48/1.55      ( ~ v2_struct_0(sK3) ),
% 7.48/1.55      inference(cnf_transformation,[],[f82]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_79,plain,
% 7.48/1.55      ( v2_struct_0(sK3) != iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_72]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_71,negated_conjecture,
% 7.48/1.55      ( v2_pre_topc(sK3) ),
% 7.48/1.55      inference(cnf_transformation,[],[f83]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_80,plain,
% 7.48/1.55      ( v2_pre_topc(sK3) = iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_71]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_70,negated_conjecture,
% 7.48/1.55      ( l1_pre_topc(sK3) ),
% 7.48/1.55      inference(cnf_transformation,[],[f84]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_81,plain,
% 7.48/1.55      ( l1_pre_topc(sK3) = iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_70]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_82,plain,
% 7.48/1.55      ( v1_funct_1(sK4) = iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_69]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_68,negated_conjecture,
% 7.48/1.55      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 7.48/1.55      inference(cnf_transformation,[],[f86]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_83,plain,
% 7.48/1.55      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_68]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_11339,plain,
% 7.48/1.55      ( m1_pre_topc(X0_54,sK2) != iProver_top
% 7.48/1.55      | k2_tmap_1(sK2,sK3,sK4,X0_54) = k7_relat_1(sK4,u1_struct_0(X0_54)) ),
% 7.48/1.55      inference(global_propositional_subsumption,
% 7.48/1.55                [status(thm)],
% 7.48/1.55                [c_6994,c_76,c_77,c_78,c_79,c_80,c_81,c_82,c_83]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_11340,plain,
% 7.48/1.55      ( k2_tmap_1(sK2,sK3,sK4,X0_54) = k7_relat_1(sK4,u1_struct_0(X0_54))
% 7.48/1.55      | m1_pre_topc(X0_54,sK2) != iProver_top ),
% 7.48/1.55      inference(renaming,[status(thm)],[c_11339]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_11350,plain,
% 7.48/1.55      ( k2_tmap_1(sK2,sK3,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 7.48/1.55      inference(superposition,[status(thm)],[c_7466,c_11340]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3,plain,
% 7.48/1.55      ( v4_relat_1(X0,X1)
% 7.48/1.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.48/1.55      inference(cnf_transformation,[],[f54]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2,plain,
% 7.48/1.55      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.48/1.55      inference(cnf_transformation,[],[f53]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_761,plain,
% 7.48/1.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.48/1.55      | ~ v1_relat_1(X0)
% 7.48/1.55      | k7_relat_1(X0,X1) = X0 ),
% 7.48/1.55      inference(resolution,[status(thm)],[c_3,c_2]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2377,plain,
% 7.48/1.55      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 7.48/1.55      | ~ v1_relat_1(X0_55)
% 7.48/1.55      | k7_relat_1(X0_55,X0_56) = X0_55 ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_761]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3377,plain,
% 7.48/1.55      ( k7_relat_1(X0_55,X0_56) = X0_55
% 7.48/1.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 7.48/1.55      | v1_relat_1(X0_55) != iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_2377]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_1,plain,
% 7.48/1.55      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.48/1.55      inference(cnf_transformation,[],[f52]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2419,plain,
% 7.48/1.55      ( v1_relat_1(k2_zfmisc_1(X0_56,X1_56)) ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_1]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2466,plain,
% 7.48/1.55      ( v1_relat_1(k2_zfmisc_1(X0_56,X1_56)) = iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_2419]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2529,plain,
% 7.48/1.55      ( k7_relat_1(X0_55,X0_56) = X0_55
% 7.48/1.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 7.48/1.55      | v1_relat_1(X0_55) != iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_2377]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_0,plain,
% 7.48/1.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.48/1.55      | ~ v1_relat_1(X1)
% 7.48/1.55      | v1_relat_1(X0) ),
% 7.48/1.55      inference(cnf_transformation,[],[f51]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2420,plain,
% 7.48/1.55      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
% 7.48/1.55      | ~ v1_relat_1(X1_55)
% 7.48/1.55      | v1_relat_1(X0_55) ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_0]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3851,plain,
% 7.48/1.55      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 7.48/1.55      | v1_relat_1(X0_55)
% 7.48/1.55      | ~ v1_relat_1(k2_zfmisc_1(X0_56,X1_56)) ),
% 7.48/1.55      inference(instantiation,[status(thm)],[c_2420]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3852,plain,
% 7.48/1.55      ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 7.48/1.55      | v1_relat_1(X0_55) = iProver_top
% 7.48/1.55      | v1_relat_1(k2_zfmisc_1(X0_56,X1_56)) != iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_3851]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_9241,plain,
% 7.48/1.55      ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 7.48/1.55      | k7_relat_1(X0_55,X0_56) = X0_55 ),
% 7.48/1.55      inference(global_propositional_subsumption,
% 7.48/1.55                [status(thm)],
% 7.48/1.55                [c_3377,c_2466,c_2529,c_3852]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_9242,plain,
% 7.48/1.55      ( k7_relat_1(X0_55,X0_56) = X0_55
% 7.48/1.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
% 7.48/1.55      inference(renaming,[status(thm)],[c_9241]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_9251,plain,
% 7.48/1.55      ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK4 ),
% 7.48/1.55      inference(superposition,[status(thm)],[c_3367,c_9242]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_11352,plain,
% 7.48/1.55      ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4 ),
% 7.48/1.55      inference(light_normalisation,[status(thm)],[c_11350,c_9251]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_10,plain,
% 7.48/1.55      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.48/1.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.48/1.55      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 7.48/1.55      | ~ l1_struct_0(X3)
% 7.48/1.55      | ~ l1_struct_0(X2)
% 7.48/1.55      | ~ l1_struct_0(X1)
% 7.48/1.55      | ~ v1_funct_1(X0) ),
% 7.48/1.55      inference(cnf_transformation,[],[f63]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2412,plain,
% 7.48/1.55      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.48/1.55      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.48/1.55      | m1_subset_1(k2_tmap_1(X0_54,X1_54,X0_55,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 7.48/1.55      | ~ l1_struct_0(X2_54)
% 7.48/1.55      | ~ l1_struct_0(X1_54)
% 7.48/1.55      | ~ l1_struct_0(X0_54)
% 7.48/1.55      | ~ v1_funct_1(X0_55) ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_10]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3343,plain,
% 7.48/1.55      ( v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.48/1.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.48/1.55      | m1_subset_1(k2_tmap_1(X0_54,X1_54,X0_55,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) = iProver_top
% 7.48/1.55      | l1_struct_0(X2_54) != iProver_top
% 7.48/1.55      | l1_struct_0(X1_54) != iProver_top
% 7.48/1.55      | l1_struct_0(X0_54) != iProver_top
% 7.48/1.55      | v1_funct_1(X0_55) != iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_2412]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_17,plain,
% 7.48/1.55      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.48/1.55      | sP0(X4,X3,X2,X1,X0)
% 7.48/1.55      | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
% 7.48/1.55      | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
% 7.48/1.55      | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
% 7.48/1.55      | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
% 7.48/1.55      inference(cnf_transformation,[],[f64]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_27,plain,
% 7.48/1.55      ( sP1(X0,X1,X2,X3,X4)
% 7.48/1.55      | ~ r4_tsep_1(X1,X0,X3)
% 7.48/1.55      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
% 7.48/1.55      | ~ m1_pre_topc(X3,X1)
% 7.48/1.55      | ~ m1_pre_topc(X0,X1)
% 7.48/1.55      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 7.48/1.55      | v2_struct_0(X1)
% 7.48/1.55      | v2_struct_0(X4)
% 7.48/1.55      | v2_struct_0(X0)
% 7.48/1.55      | v2_struct_0(X3)
% 7.48/1.55      | ~ v2_pre_topc(X4)
% 7.48/1.55      | ~ v2_pre_topc(X1)
% 7.48/1.55      | ~ l1_pre_topc(X1)
% 7.48/1.55      | ~ l1_pre_topc(X4)
% 7.48/1.55      | ~ v1_funct_1(X2) ),
% 7.48/1.55      inference(cnf_transformation,[],[f78]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_61,negated_conjecture,
% 7.48/1.55      ( r4_tsep_1(sK2,sK5,sK6) ),
% 7.48/1.55      inference(cnf_transformation,[],[f93]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_779,plain,
% 7.48/1.55      ( sP1(X0,X1,X2,X3,X4)
% 7.48/1.55      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
% 7.48/1.55      | ~ m1_pre_topc(X0,X1)
% 7.48/1.55      | ~ m1_pre_topc(X3,X1)
% 7.48/1.55      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 7.48/1.55      | v2_struct_0(X1)
% 7.48/1.55      | v2_struct_0(X0)
% 7.48/1.55      | v2_struct_0(X3)
% 7.48/1.55      | v2_struct_0(X4)
% 7.48/1.55      | ~ v2_pre_topc(X1)
% 7.48/1.55      | ~ v2_pre_topc(X4)
% 7.48/1.55      | ~ l1_pre_topc(X1)
% 7.48/1.55      | ~ l1_pre_topc(X4)
% 7.48/1.55      | ~ v1_funct_1(X2)
% 7.48/1.55      | sK5 != X0
% 7.48/1.55      | sK6 != X3
% 7.48/1.55      | sK2 != X1 ),
% 7.48/1.55      inference(resolution_lifted,[status(thm)],[c_27,c_61]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_780,plain,
% 7.48/1.55      ( sP1(sK5,sK2,X0,sK6,X1)
% 7.48/1.55      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 7.48/1.55      | ~ m1_pre_topc(sK5,sK2)
% 7.48/1.55      | ~ m1_pre_topc(sK6,sK2)
% 7.48/1.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 7.48/1.55      | v2_struct_0(X1)
% 7.48/1.55      | v2_struct_0(sK5)
% 7.48/1.55      | v2_struct_0(sK6)
% 7.48/1.55      | v2_struct_0(sK2)
% 7.48/1.55      | ~ v2_pre_topc(X1)
% 7.48/1.55      | ~ v2_pre_topc(sK2)
% 7.48/1.55      | ~ l1_pre_topc(X1)
% 7.48/1.55      | ~ l1_pre_topc(sK2)
% 7.48/1.55      | ~ v1_funct_1(X0) ),
% 7.48/1.55      inference(unflattening,[status(thm)],[c_779]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_784,plain,
% 7.48/1.55      ( ~ l1_pre_topc(X1)
% 7.48/1.55      | v2_struct_0(X1)
% 7.48/1.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 7.48/1.55      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 7.48/1.55      | sP1(sK5,sK2,X0,sK6,X1)
% 7.48/1.55      | ~ v2_pre_topc(X1)
% 7.48/1.55      | ~ v1_funct_1(X0) ),
% 7.48/1.55      inference(global_propositional_subsumption,
% 7.48/1.55                [status(thm)],
% 7.48/1.55                [c_780,c_75,c_74,c_73,c_66,c_65,c_64,c_63]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_785,plain,
% 7.48/1.55      ( sP1(sK5,sK2,X0,sK6,X1)
% 7.48/1.55      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 7.48/1.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 7.48/1.55      | v2_struct_0(X1)
% 7.48/1.55      | ~ v2_pre_topc(X1)
% 7.48/1.55      | ~ l1_pre_topc(X1)
% 7.48/1.55      | ~ v1_funct_1(X0) ),
% 7.48/1.55      inference(renaming,[status(thm)],[c_784]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_820,plain,
% 7.48/1.55      ( sP0(X0,X1,X2,X3,X4)
% 7.48/1.55      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_tsep_1(X3,X4,X1),X0)
% 7.48/1.55      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 7.48/1.55      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))
% 7.48/1.55      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 7.48/1.55      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))))
% 7.48/1.55      | v2_struct_0(X6)
% 7.48/1.55      | ~ v2_pre_topc(X6)
% 7.48/1.55      | ~ l1_pre_topc(X6)
% 7.48/1.55      | ~ v1_funct_1(X5)
% 7.48/1.55      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)))
% 7.48/1.55      | X5 != X2
% 7.48/1.55      | X6 != X0
% 7.48/1.55      | sK5 != X4
% 7.48/1.55      | sK6 != X1
% 7.48/1.55      | sK2 != X3 ),
% 7.48/1.55      inference(resolution_lifted,[status(thm)],[c_17,c_785]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_821,plain,
% 7.48/1.55      ( sP0(X0,sK6,X1,sK2,sK5)
% 7.48/1.55      | ~ v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
% 7.48/1.55      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 7.48/1.55      | ~ v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))
% 7.48/1.55      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 7.48/1.55      | ~ m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
% 7.48/1.55      | v2_struct_0(X0)
% 7.48/1.55      | ~ v2_pre_topc(X0)
% 7.48/1.55      | ~ l1_pre_topc(X0)
% 7.48/1.55      | ~ v1_funct_1(X1)
% 7.48/1.55      | ~ v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) ),
% 7.48/1.55      inference(unflattening,[status(thm)],[c_820]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2376,plain,
% 7.48/1.55      ( sP0(X0_54,sK6,X0_55,sK2,sK5)
% 7.48/1.55      | ~ v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_54)
% 7.48/1.55      | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
% 7.48/1.55      | ~ v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54))
% 7.48/1.55      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
% 7.48/1.55      | ~ m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54))))
% 7.48/1.55      | v2_struct_0(X0_54)
% 7.48/1.55      | ~ v2_pre_topc(X0_54)
% 7.48/1.55      | ~ l1_pre_topc(X0_54)
% 7.48/1.55      | ~ v1_funct_1(X0_55)
% 7.48/1.55      | ~ v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6))) ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_821]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3378,plain,
% 7.48/1.55      ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_54) != iProver_top
% 7.48/1.55      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.48/1.55      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54)) != iProver_top
% 7.48/1.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.48/1.55      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54)))) != iProver_top
% 7.48/1.55      | v2_struct_0(X0_54) = iProver_top
% 7.48/1.55      | v2_pre_topc(X0_54) != iProver_top
% 7.48/1.55      | l1_pre_topc(X0_54) != iProver_top
% 7.48/1.55      | v1_funct_1(X0_55) != iProver_top
% 7.48/1.55      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6))) != iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_2376]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3701,plain,
% 7.48/1.55      ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) != iProver_top
% 7.48/1.55      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.48/1.55      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.48/1.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.48/1.55      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.48/1.55      | v2_struct_0(X0_54) = iProver_top
% 7.48/1.55      | v2_pre_topc(X0_54) != iProver_top
% 7.48/1.55      | l1_pre_topc(X0_54) != iProver_top
% 7.48/1.55      | v1_funct_1(X0_55) != iProver_top
% 7.48/1.55      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) != iProver_top ),
% 7.48/1.55      inference(light_normalisation,[status(thm)],[c_3378,c_2392]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_8522,plain,
% 7.48/1.55      ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) != iProver_top
% 7.48/1.55      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.48/1.55      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.48/1.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.48/1.55      | v2_struct_0(X0_54) = iProver_top
% 7.48/1.55      | v2_pre_topc(X0_54) != iProver_top
% 7.48/1.55      | l1_pre_topc(X0_54) != iProver_top
% 7.48/1.55      | l1_struct_0(X0_54) != iProver_top
% 7.48/1.55      | l1_struct_0(sK2) != iProver_top
% 7.48/1.55      | v1_funct_1(X0_55) != iProver_top
% 7.48/1.55      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) != iProver_top ),
% 7.48/1.55      inference(superposition,[status(thm)],[c_3343,c_3701]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_5,plain,
% 7.48/1.55      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.48/1.55      inference(cnf_transformation,[],[f56]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2417,plain,
% 7.48/1.55      ( ~ l1_pre_topc(X0_54) | l1_struct_0(X0_54) ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_5]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2472,plain,
% 7.48/1.55      ( l1_pre_topc(X0_54) != iProver_top
% 7.48/1.55      | l1_struct_0(X0_54) = iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_2417]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3983,plain,
% 7.48/1.55      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 7.48/1.55      inference(instantiation,[status(thm)],[c_2417]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3984,plain,
% 7.48/1.55      ( l1_pre_topc(sK2) != iProver_top
% 7.48/1.55      | l1_struct_0(sK2) = iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_3983]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_9121,plain,
% 7.48/1.55      ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) != iProver_top
% 7.48/1.55      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.48/1.55      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.48/1.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.48/1.55      | v2_struct_0(X0_54) = iProver_top
% 7.48/1.55      | v2_pre_topc(X0_54) != iProver_top
% 7.48/1.55      | l1_pre_topc(X0_54) != iProver_top
% 7.48/1.55      | v1_funct_1(X0_55) != iProver_top
% 7.48/1.55      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) != iProver_top ),
% 7.48/1.55      inference(global_propositional_subsumption,
% 7.48/1.55                [status(thm)],
% 7.48/1.55                [c_8522,c_78,c_2472,c_3984]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_17542,plain,
% 7.48/1.55      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
% 7.48/1.55      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.48/1.55      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.48/1.55      | v2_struct_0(sK3) = iProver_top
% 7.48/1.55      | v2_pre_topc(sK3) != iProver_top
% 7.48/1.55      | l1_pre_topc(sK3) != iProver_top
% 7.48/1.55      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
% 7.48/1.55      | v1_funct_1(sK4) != iProver_top ),
% 7.48/1.55      inference(superposition,[status(thm)],[c_11352,c_9121]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_17598,plain,
% 7.48/1.55      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 7.48/1.55      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.48/1.55      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.48/1.55      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.48/1.55      | v2_struct_0(sK3) = iProver_top
% 7.48/1.55      | v2_pre_topc(sK3) != iProver_top
% 7.48/1.55      | l1_pre_topc(sK3) != iProver_top
% 7.48/1.55      | v1_funct_1(sK4) != iProver_top ),
% 7.48/1.55      inference(light_normalisation,[status(thm)],[c_17542,c_11352]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_17713,plain,
% 7.48/1.55      ( sP0(sK3,sK6,sK4,sK2,sK5)
% 7.48/1.55      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.48/1.55      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.48/1.55      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.48/1.55      | v2_struct_0(sK3)
% 7.48/1.55      | ~ v2_pre_topc(sK3)
% 7.48/1.55      | ~ l1_pre_topc(sK3)
% 7.48/1.55      | ~ v1_funct_1(sK4) ),
% 7.48/1.55      inference(predicate_to_equality_rev,[status(thm)],[c_17598]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_13,plain,
% 7.48/1.55      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.48/1.55      | ~ sP0(X4,X3,X2,X1,X0)
% 7.48/1.55      | m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) ),
% 7.48/1.55      inference(cnf_transformation,[],[f68]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_949,plain,
% 7.48/1.55      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.48/1.55      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 7.48/1.55      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 7.48/1.55      | m1_subset_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))))
% 7.48/1.55      | v2_struct_0(X6)
% 7.48/1.55      | ~ v2_pre_topc(X6)
% 7.48/1.55      | ~ l1_pre_topc(X6)
% 7.48/1.55      | ~ v1_funct_1(X5)
% 7.48/1.55      | X5 != X2
% 7.48/1.55      | X6 != X0
% 7.48/1.55      | sK5 != X4
% 7.48/1.55      | sK6 != X1
% 7.48/1.55      | sK2 != X3 ),
% 7.48/1.55      inference(resolution_lifted,[status(thm)],[c_13,c_785]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_950,plain,
% 7.48/1.55      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 7.48/1.55      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 7.48/1.55      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 7.48/1.55      | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
% 7.48/1.55      | v2_struct_0(X0)
% 7.48/1.55      | ~ v2_pre_topc(X0)
% 7.48/1.55      | ~ l1_pre_topc(X0)
% 7.48/1.55      | ~ v1_funct_1(X1) ),
% 7.48/1.55      inference(unflattening,[status(thm)],[c_949]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2372,plain,
% 7.48/1.55      ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
% 7.48/1.55      | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
% 7.48/1.55      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
% 7.48/1.55      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54))))
% 7.48/1.55      | v2_struct_0(X0_54)
% 7.48/1.55      | ~ v2_pre_topc(X0_54)
% 7.48/1.55      | ~ l1_pre_topc(X0_54)
% 7.48/1.55      | ~ v1_funct_1(X0_55) ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_950]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3382,plain,
% 7.48/1.55      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 7.48/1.55      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.48/1.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.48/1.55      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54)))) = iProver_top
% 7.48/1.55      | v2_struct_0(X0_54) = iProver_top
% 7.48/1.55      | v2_pre_topc(X0_54) != iProver_top
% 7.48/1.55      | l1_pre_topc(X0_54) != iProver_top
% 7.48/1.55      | v1_funct_1(X0_55) != iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_2372]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3626,plain,
% 7.48/1.55      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 7.48/1.55      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.48/1.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.48/1.55      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) = iProver_top
% 7.48/1.55      | v2_struct_0(X0_54) = iProver_top
% 7.48/1.55      | v2_pre_topc(X0_54) != iProver_top
% 7.48/1.55      | l1_pre_topc(X0_54) != iProver_top
% 7.48/1.55      | v1_funct_1(X0_55) != iProver_top ),
% 7.48/1.55      inference(light_normalisation,[status(thm)],[c_3382,c_2392]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_30,negated_conjecture,
% 7.48/1.55      ( v5_pre_topc(sK4,sK2,sK3)
% 7.48/1.55      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 7.48/1.55      inference(cnf_transformation,[],[f124]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2400,negated_conjecture,
% 7.48/1.55      ( v5_pre_topc(sK4,sK2,sK3)
% 7.48/1.55      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_30]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3355,plain,
% 7.48/1.55      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.48/1.55      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_2400]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_18,plain,
% 7.48/1.55      ( sP0(X0,X1,X2,X3,X4)
% 7.48/1.55      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
% 7.48/1.55      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
% 7.48/1.55      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
% 7.48/1.55      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
% 7.48/1.55      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 7.48/1.55      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
% 7.48/1.55      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
% 7.48/1.55      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
% 7.48/1.55      inference(cnf_transformation,[],[f77]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2409,plain,
% 7.48/1.55      ( sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
% 7.48/1.55      | ~ v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),X1_54,X0_54)
% 7.48/1.55      | ~ v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),X3_54,X0_54)
% 7.48/1.55      | ~ v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),u1_struct_0(X1_54),u1_struct_0(X0_54))
% 7.48/1.55      | ~ v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),u1_struct_0(X3_54),u1_struct_0(X0_54))
% 7.48/1.55      | ~ m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54))))
% 7.48/1.55      | ~ m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X0_54))))
% 7.48/1.55      | ~ v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_55,X1_54))
% 7.48/1.55      | ~ v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_55,X3_54)) ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_18]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3346,plain,
% 7.48/1.55      ( sP0(X0_54,X1_54,X0_55,X2_54,X3_54) = iProver_top
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),X1_54,X0_54) != iProver_top
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),X3_54,X0_54) != iProver_top
% 7.48/1.55      | v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top
% 7.48/1.55      | v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),u1_struct_0(X3_54),u1_struct_0(X0_54)) != iProver_top
% 7.48/1.55      | m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
% 7.48/1.55      | m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X0_54)))) != iProver_top
% 7.48/1.55      | v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_55,X1_54)) != iProver_top
% 7.48/1.55      | v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_55,X3_54)) != iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_2409]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_8821,plain,
% 7.48/1.55      ( sP0(sK3,sK6,sK4,sK2,X0_54) = iProver_top
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_54),X0_54,sK3) != iProver_top
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.48/1.55      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.48/1.55      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_54),u1_struct_0(X0_54),u1_struct_0(sK3)) != iProver_top
% 7.48/1.55      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.48/1.55      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3)))) != iProver_top
% 7.48/1.55      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54)) != iProver_top
% 7.48/1.55      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 7.48/1.55      inference(superposition,[status(thm)],[c_3355,c_3346]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_84,plain,
% 7.48/1.55      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_67]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_38,negated_conjecture,
% 7.48/1.55      ( v5_pre_topc(sK4,sK2,sK3)
% 7.48/1.55      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
% 7.48/1.55      inference(cnf_transformation,[],[f116]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_112,plain,
% 7.48/1.55      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.48/1.55      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_34,negated_conjecture,
% 7.48/1.55      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.48/1.55      | v5_pre_topc(sK4,sK2,sK3) ),
% 7.48/1.55      inference(cnf_transformation,[],[f120]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_116,plain,
% 7.48/1.55      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
% 7.48/1.55      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_179,plain,
% 7.48/1.55      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_181,plain,
% 7.48/1.55      ( l1_pre_topc(sK3) != iProver_top
% 7.48/1.55      | l1_struct_0(sK3) = iProver_top ),
% 7.48/1.55      inference(instantiation,[status(thm)],[c_179]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2391,negated_conjecture,
% 7.48/1.55      ( m1_pre_topc(sK6,sK2) ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_63]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3363,plain,
% 7.48/1.55      ( m1_pre_topc(sK6,sK2) = iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_2391]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_6,plain,
% 7.48/1.55      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.48/1.55      inference(cnf_transformation,[],[f57]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2416,plain,
% 7.48/1.55      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.48/1.55      | ~ l1_pre_topc(X1_54)
% 7.48/1.55      | l1_pre_topc(X0_54) ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_6]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3339,plain,
% 7.48/1.55      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.48/1.55      | l1_pre_topc(X1_54) != iProver_top
% 7.48/1.55      | l1_pre_topc(X0_54) = iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_2416]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_4463,plain,
% 7.48/1.55      ( l1_pre_topc(sK6) = iProver_top
% 7.48/1.55      | l1_pre_topc(sK2) != iProver_top ),
% 7.48/1.55      inference(superposition,[status(thm)],[c_3363,c_3339]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_6173,plain,
% 7.48/1.55      ( l1_pre_topc(sK6) = iProver_top ),
% 7.48/1.55      inference(global_propositional_subsumption,
% 7.48/1.55                [status(thm)],
% 7.48/1.55                [c_4463,c_78]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3338,plain,
% 7.48/1.55      ( l1_pre_topc(X0_54) != iProver_top
% 7.48/1.55      | l1_struct_0(X0_54) = iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_2417]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_6178,plain,
% 7.48/1.55      ( l1_struct_0(sK6) = iProver_top ),
% 7.48/1.55      inference(superposition,[status(thm)],[c_6173,c_3338]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_12,plain,
% 7.48/1.55      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.48/1.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.48/1.55      | ~ l1_struct_0(X3)
% 7.48/1.55      | ~ l1_struct_0(X2)
% 7.48/1.55      | ~ l1_struct_0(X1)
% 7.48/1.55      | ~ v1_funct_1(X0)
% 7.48/1.55      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 7.48/1.55      inference(cnf_transformation,[],[f61]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2410,plain,
% 7.48/1.55      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.48/1.55      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.48/1.55      | ~ l1_struct_0(X2_54)
% 7.48/1.55      | ~ l1_struct_0(X1_54)
% 7.48/1.55      | ~ l1_struct_0(X0_54)
% 7.48/1.55      | ~ v1_funct_1(X0_55)
% 7.48/1.55      | v1_funct_1(k2_tmap_1(X0_54,X1_54,X0_55,X2_54)) ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_12]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3940,plain,
% 7.48/1.55      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.48/1.55      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.48/1.55      | ~ l1_struct_0(X0_54)
% 7.48/1.55      | ~ l1_struct_0(sK3)
% 7.48/1.55      | ~ l1_struct_0(sK2)
% 7.48/1.55      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54))
% 7.48/1.55      | ~ v1_funct_1(sK4) ),
% 7.48/1.55      inference(instantiation,[status(thm)],[c_2410]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_6185,plain,
% 7.48/1.55      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.48/1.55      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.48/1.55      | ~ l1_struct_0(sK6)
% 7.48/1.55      | ~ l1_struct_0(sK3)
% 7.48/1.55      | ~ l1_struct_0(sK2)
% 7.48/1.55      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 7.48/1.55      | ~ v1_funct_1(sK4) ),
% 7.48/1.55      inference(instantiation,[status(thm)],[c_3940]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_6186,plain,
% 7.48/1.55      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.48/1.55      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.48/1.55      | l1_struct_0(sK6) != iProver_top
% 7.48/1.55      | l1_struct_0(sK3) != iProver_top
% 7.48/1.55      | l1_struct_0(sK2) != iProver_top
% 7.48/1.55      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top
% 7.48/1.55      | v1_funct_1(sK4) != iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_6185]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_9702,plain,
% 7.48/1.55      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54)) != iProver_top
% 7.48/1.55      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3)))) != iProver_top
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_54),X0_54,sK3) != iProver_top
% 7.48/1.55      | sP0(sK3,sK6,sK4,sK2,X0_54) = iProver_top
% 7.48/1.55      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.48/1.55      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_54),u1_struct_0(X0_54),u1_struct_0(sK3)) != iProver_top ),
% 7.48/1.55      inference(global_propositional_subsumption,
% 7.48/1.55                [status(thm)],
% 7.48/1.55                [c_8821,c_78,c_81,c_82,c_83,c_84,c_112,c_116,c_181,
% 7.48/1.55                 c_3984,c_6178,c_6186]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_9703,plain,
% 7.48/1.55      ( sP0(sK3,sK6,sK4,sK2,X0_54) = iProver_top
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_54),X0_54,sK3) != iProver_top
% 7.48/1.55      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.48/1.55      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_54),u1_struct_0(X0_54),u1_struct_0(sK3)) != iProver_top
% 7.48/1.55      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3)))) != iProver_top
% 7.48/1.55      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54)) != iProver_top ),
% 7.48/1.55      inference(renaming,[status(thm)],[c_9702]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_9717,plain,
% 7.48/1.55      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.48/1.55      | sP0(sK3,sK6,sK4,sK2,sK2) = iProver_top
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
% 7.48/1.55      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.48/1.55      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.48/1.55      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.48/1.55      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.48/1.55      | v2_struct_0(sK3) = iProver_top
% 7.48/1.55      | v2_pre_topc(sK3) != iProver_top
% 7.48/1.55      | l1_pre_topc(sK3) != iProver_top
% 7.48/1.55      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
% 7.48/1.55      | v1_funct_1(sK4) != iProver_top ),
% 7.48/1.55      inference(superposition,[status(thm)],[c_3626,c_9703]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_15,plain,
% 7.48/1.55      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.48/1.55      | ~ sP0(X4,X3,X2,X1,X0)
% 7.48/1.55      | v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) ),
% 7.48/1.55      inference(cnf_transformation,[],[f66]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_889,plain,
% 7.48/1.55      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.48/1.55      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 7.48/1.55      | v1_funct_2(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))
% 7.48/1.55      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 7.48/1.55      | v2_struct_0(X6)
% 7.48/1.55      | ~ v2_pre_topc(X6)
% 7.48/1.55      | ~ l1_pre_topc(X6)
% 7.48/1.55      | ~ v1_funct_1(X5)
% 7.48/1.55      | X5 != X2
% 7.48/1.55      | X6 != X0
% 7.48/1.55      | sK5 != X4
% 7.48/1.55      | sK6 != X1
% 7.48/1.55      | sK2 != X3 ),
% 7.48/1.55      inference(resolution_lifted,[status(thm)],[c_15,c_785]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_890,plain,
% 7.48/1.55      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 7.48/1.55      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 7.48/1.55      | v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))
% 7.48/1.55      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 7.48/1.55      | v2_struct_0(X0)
% 7.48/1.55      | ~ v2_pre_topc(X0)
% 7.48/1.55      | ~ l1_pre_topc(X0)
% 7.48/1.55      | ~ v1_funct_1(X1) ),
% 7.48/1.55      inference(unflattening,[status(thm)],[c_889]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2374,plain,
% 7.48/1.55      ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
% 7.48/1.55      | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
% 7.48/1.55      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54))
% 7.48/1.55      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
% 7.48/1.55      | v2_struct_0(X0_54)
% 7.48/1.55      | ~ v2_pre_topc(X0_54)
% 7.48/1.55      | ~ l1_pre_topc(X0_54)
% 7.48/1.55      | ~ v1_funct_1(X0_55) ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_890]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3380,plain,
% 7.48/1.55      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 7.48/1.55      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.48/1.55      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54)) = iProver_top
% 7.48/1.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.48/1.55      | v2_struct_0(X0_54) = iProver_top
% 7.48/1.55      | v2_pre_topc(X0_54) != iProver_top
% 7.48/1.55      | l1_pre_topc(X0_54) != iProver_top
% 7.48/1.55      | v1_funct_1(X0_55) != iProver_top ),
% 7.48/1.55      inference(predicate_to_equality,[status(thm)],[c_2374]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3609,plain,
% 7.48/1.55      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 7.48/1.55      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.48/1.55      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) = iProver_top
% 7.48/1.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.48/1.55      | v2_struct_0(X0_54) = iProver_top
% 7.48/1.55      | v2_pre_topc(X0_54) != iProver_top
% 7.48/1.55      | l1_pre_topc(X0_54) != iProver_top
% 7.48/1.55      | v1_funct_1(X0_55) != iProver_top ),
% 7.48/1.55      inference(light_normalisation,[status(thm)],[c_3380,c_2392]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3774,plain,
% 7.48/1.55      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.48/1.55      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
% 7.48/1.55      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.48/1.55      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.48/1.55      | v2_struct_0(sK3) = iProver_top
% 7.48/1.55      | v2_pre_topc(sK3) != iProver_top
% 7.48/1.55      | l1_pre_topc(sK3) != iProver_top
% 7.48/1.55      | v1_funct_1(sK4) != iProver_top ),
% 7.48/1.55      inference(instantiation,[status(thm)],[c_3609]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_14,plain,
% 7.48/1.55      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.48/1.55      | ~ sP0(X4,X3,X2,X1,X0)
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) ),
% 7.48/1.55      inference(cnf_transformation,[],[f67]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_919,plain,
% 7.48/1.55      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_tsep_1(X3,X4,X1),X0)
% 7.48/1.55      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 7.48/1.55      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 7.48/1.55      | v2_struct_0(X6)
% 7.48/1.55      | ~ v2_pre_topc(X6)
% 7.48/1.55      | ~ l1_pre_topc(X6)
% 7.48/1.55      | ~ v1_funct_1(X5)
% 7.48/1.55      | X5 != X2
% 7.48/1.55      | X6 != X0
% 7.48/1.55      | sK5 != X4
% 7.48/1.55      | sK6 != X1
% 7.48/1.55      | sK2 != X3 ),
% 7.48/1.55      inference(resolution_lifted,[status(thm)],[c_14,c_785]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_920,plain,
% 7.48/1.55      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
% 7.48/1.55      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 7.48/1.55      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 7.48/1.55      | v2_struct_0(X0)
% 7.48/1.55      | ~ v2_pre_topc(X0)
% 7.48/1.55      | ~ l1_pre_topc(X0)
% 7.48/1.55      | ~ v1_funct_1(X1) ),
% 7.48/1.55      inference(unflattening,[status(thm)],[c_919]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_2373,plain,
% 7.48/1.55      ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_54)
% 7.48/1.55      | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
% 7.48/1.55      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
% 7.48/1.55      | v2_struct_0(X0_54)
% 7.48/1.55      | ~ v2_pre_topc(X0_54)
% 7.48/1.55      | ~ l1_pre_topc(X0_54)
% 7.48/1.55      | ~ v1_funct_1(X0_55) ),
% 7.48/1.55      inference(subtyping,[status(esa)],[c_920]) ).
% 7.48/1.55  
% 7.48/1.55  cnf(c_3381,plain,
% 7.48/1.55      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 7.48/1.55      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_54) = iProver_top
% 7.48/1.56      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.48/1.56      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.48/1.56      | v2_struct_0(X0_54) = iProver_top
% 7.48/1.56      | v2_pre_topc(X0_54) != iProver_top
% 7.48/1.56      | l1_pre_topc(X0_54) != iProver_top
% 7.48/1.56      | v1_funct_1(X0_55) != iProver_top ),
% 7.48/1.56      inference(predicate_to_equality,[status(thm)],[c_2373]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_3592,plain,
% 7.48/1.56      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 7.48/1.56      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) = iProver_top
% 7.48/1.56      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.48/1.56      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.48/1.56      | v2_struct_0(X0_54) = iProver_top
% 7.48/1.56      | v2_pre_topc(X0_54) != iProver_top
% 7.48/1.56      | l1_pre_topc(X0_54) != iProver_top
% 7.48/1.56      | v1_funct_1(X0_55) != iProver_top ),
% 7.48/1.56      inference(light_normalisation,[status(thm)],[c_3381,c_2392]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_4985,plain,
% 7.48/1.56      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.48/1.56      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
% 7.48/1.56      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.48/1.56      | v2_struct_0(sK3) = iProver_top
% 7.48/1.56      | v2_pre_topc(sK3) != iProver_top
% 7.48/1.56      | l1_pre_topc(sK3) != iProver_top
% 7.48/1.56      | v1_funct_1(sK4) != iProver_top ),
% 7.48/1.56      inference(superposition,[status(thm)],[c_3367,c_3592]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_7941,plain,
% 7.48/1.56      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
% 7.48/1.56      | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top ),
% 7.48/1.56      inference(global_propositional_subsumption,
% 7.48/1.56                [status(thm)],
% 7.48/1.56                [c_4985,c_79,c_80,c_81,c_82,c_83]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_7942,plain,
% 7.48/1.56      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.48/1.56      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top ),
% 7.48/1.56      inference(renaming,[status(thm)],[c_7941]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_46,negated_conjecture,
% 7.48/1.56      ( v5_pre_topc(sK4,sK2,sK3)
% 7.48/1.56      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 7.48/1.56      inference(cnf_transformation,[],[f108]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_2396,negated_conjecture,
% 7.48/1.56      ( v5_pre_topc(sK4,sK2,sK3)
% 7.48/1.56      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 7.48/1.56      inference(subtyping,[status(esa)],[c_46]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_3359,plain,
% 7.48/1.56      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.48/1.56      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 7.48/1.56      inference(predicate_to_equality,[status(thm)],[c_2396]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_9715,plain,
% 7.48/1.56      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 7.48/1.56      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.48/1.56      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.48/1.56      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.48/1.56      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top ),
% 7.48/1.56      inference(superposition,[status(thm)],[c_3359,c_9703]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_54,negated_conjecture,
% 7.48/1.56      ( v5_pre_topc(sK4,sK2,sK3)
% 7.48/1.56      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 7.48/1.56      inference(cnf_transformation,[],[f100]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_96,plain,
% 7.48/1.56      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.48/1.56      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 7.48/1.56      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_50,negated_conjecture,
% 7.48/1.56      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.48/1.56      | v5_pre_topc(sK4,sK2,sK3) ),
% 7.48/1.56      inference(cnf_transformation,[],[f104]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_100,plain,
% 7.48/1.56      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
% 7.48/1.56      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.48/1.56      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_4261,plain,
% 7.48/1.56      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.48/1.56      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.48/1.56      | ~ l1_struct_0(sK5)
% 7.48/1.56      | ~ l1_struct_0(sK3)
% 7.48/1.56      | ~ l1_struct_0(sK2)
% 7.48/1.56      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.48/1.56      | ~ v1_funct_1(sK4) ),
% 7.48/1.56      inference(instantiation,[status(thm)],[c_3940]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_4262,plain,
% 7.48/1.56      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.48/1.56      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.48/1.56      | l1_struct_0(sK5) != iProver_top
% 7.48/1.56      | l1_struct_0(sK3) != iProver_top
% 7.48/1.56      | l1_struct_0(sK2) != iProver_top
% 7.48/1.56      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top
% 7.48/1.56      | v1_funct_1(sK4) != iProver_top ),
% 7.48/1.56      inference(predicate_to_equality,[status(thm)],[c_4261]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_2389,negated_conjecture,
% 7.48/1.56      ( m1_pre_topc(sK5,sK2) ),
% 7.48/1.56      inference(subtyping,[status(esa)],[c_65]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_3365,plain,
% 7.48/1.56      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 7.48/1.56      inference(predicate_to_equality,[status(thm)],[c_2389]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_4464,plain,
% 7.48/1.56      ( l1_pre_topc(sK5) = iProver_top
% 7.48/1.56      | l1_pre_topc(sK2) != iProver_top ),
% 7.48/1.56      inference(superposition,[status(thm)],[c_3365,c_3339]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_4780,plain,
% 7.48/1.56      ( ~ l1_pre_topc(sK5) | l1_struct_0(sK5) ),
% 7.48/1.56      inference(instantiation,[status(thm)],[c_2417]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_4781,plain,
% 7.48/1.56      ( l1_pre_topc(sK5) != iProver_top
% 7.48/1.56      | l1_struct_0(sK5) = iProver_top ),
% 7.48/1.56      inference(predicate_to_equality,[status(thm)],[c_4780]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_9822,plain,
% 7.48/1.56      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 7.48/1.56      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.48/1.56      inference(global_propositional_subsumption,
% 7.48/1.56                [status(thm)],
% 7.48/1.56                [c_9715,c_78,c_81,c_82,c_83,c_84,c_96,c_100,c_181,c_3984,
% 7.48/1.56                 c_4262,c_4464,c_4781]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_16,plain,
% 7.48/1.56      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.48/1.56      | ~ sP0(X4,X3,X2,X1,X0)
% 7.48/1.56      | v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
% 7.48/1.56      inference(cnf_transformation,[],[f65]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_859,plain,
% 7.48/1.56      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.48/1.56      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 7.48/1.56      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 7.48/1.56      | v2_struct_0(X6)
% 7.48/1.56      | ~ v2_pre_topc(X6)
% 7.48/1.56      | ~ l1_pre_topc(X6)
% 7.48/1.56      | ~ v1_funct_1(X5)
% 7.48/1.56      | v1_funct_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)))
% 7.48/1.56      | X5 != X2
% 7.48/1.56      | X6 != X0
% 7.48/1.56      | sK5 != X4
% 7.48/1.56      | sK6 != X1
% 7.48/1.56      | sK2 != X3 ),
% 7.48/1.56      inference(resolution_lifted,[status(thm)],[c_16,c_785]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_860,plain,
% 7.48/1.56      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 7.48/1.56      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 7.48/1.56      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 7.48/1.56      | v2_struct_0(X0)
% 7.48/1.56      | ~ v2_pre_topc(X0)
% 7.48/1.56      | ~ l1_pre_topc(X0)
% 7.48/1.56      | ~ v1_funct_1(X1)
% 7.48/1.56      | v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) ),
% 7.48/1.56      inference(unflattening,[status(thm)],[c_859]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_2375,plain,
% 7.48/1.56      ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
% 7.48/1.56      | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
% 7.48/1.56      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
% 7.48/1.56      | v2_struct_0(X0_54)
% 7.48/1.56      | ~ v2_pre_topc(X0_54)
% 7.48/1.56      | ~ l1_pre_topc(X0_54)
% 7.48/1.56      | ~ v1_funct_1(X0_55)
% 7.48/1.56      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6))) ),
% 7.48/1.56      inference(subtyping,[status(esa)],[c_860]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_3379,plain,
% 7.48/1.56      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 7.48/1.56      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.48/1.56      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.48/1.56      | v2_struct_0(X0_54) = iProver_top
% 7.48/1.56      | v2_pre_topc(X0_54) != iProver_top
% 7.48/1.56      | l1_pre_topc(X0_54) != iProver_top
% 7.48/1.56      | v1_funct_1(X0_55) != iProver_top
% 7.48/1.56      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
% 7.48/1.56      inference(predicate_to_equality,[status(thm)],[c_2375]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_3575,plain,
% 7.48/1.56      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 7.48/1.56      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.48/1.56      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.48/1.56      | v2_struct_0(X0_54) = iProver_top
% 7.48/1.56      | v2_pre_topc(X0_54) != iProver_top
% 7.48/1.56      | l1_pre_topc(X0_54) != iProver_top
% 7.48/1.56      | v1_funct_1(X0_55) != iProver_top
% 7.48/1.56      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) = iProver_top ),
% 7.48/1.56      inference(light_normalisation,[status(thm)],[c_3379,c_2392]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_4772,plain,
% 7.48/1.56      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.48/1.56      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.48/1.56      | v2_struct_0(sK3) = iProver_top
% 7.48/1.56      | v2_pre_topc(sK3) != iProver_top
% 7.48/1.56      | l1_pre_topc(sK3) != iProver_top
% 7.48/1.56      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top
% 7.48/1.56      | v1_funct_1(sK4) != iProver_top ),
% 7.48/1.56      inference(superposition,[status(thm)],[c_3367,c_3575]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_7934,plain,
% 7.48/1.56      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top
% 7.48/1.56      | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top ),
% 7.48/1.56      inference(global_propositional_subsumption,
% 7.48/1.56                [status(thm)],
% 7.48/1.56                [c_4772,c_79,c_80,c_81,c_82,c_83]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_7935,plain,
% 7.48/1.56      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.48/1.56      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top ),
% 7.48/1.56      inference(renaming,[status(thm)],[c_7934]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_9839,plain,
% 7.48/1.56      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.48/1.56      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top ),
% 7.48/1.56      inference(superposition,[status(thm)],[c_9822,c_7935]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_10468,plain,
% 7.48/1.56      ( sP0(sK3,sK6,sK4,sK2,sK2) = iProver_top
% 7.48/1.56      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.48/1.56      inference(global_propositional_subsumption,
% 7.48/1.56                [status(thm)],
% 7.48/1.56                [c_9717,c_79,c_80,c_81,c_82,c_83,c_84,c_3774,c_7942,
% 7.48/1.56                 c_9822,c_9839]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_3352,plain,
% 7.48/1.56      ( sP0(X0_54,X1_54,X0_55,X2_54,X3_54) != iProver_top
% 7.48/1.56      | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),X3_54,X0_54) = iProver_top ),
% 7.48/1.56      inference(predicate_to_equality,[status(thm)],[c_2403]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_10478,plain,
% 7.48/1.56      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
% 7.48/1.56      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.48/1.56      inference(superposition,[status(thm)],[c_10468,c_3352]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_17496,plain,
% 7.48/1.56      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.48/1.56      inference(demodulation,[status(thm)],[c_11352,c_10478]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_17529,plain,
% 7.48/1.56      ( v5_pre_topc(sK4,sK2,sK3) ),
% 7.48/1.56      inference(predicate_to_equality_rev,[status(thm)],[c_17496]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_3950,plain,
% 7.48/1.56      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.48/1.56      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
% 7.48/1.56      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.48/1.56      | ~ l1_struct_0(X0_54)
% 7.48/1.56      | ~ l1_struct_0(sK3)
% 7.48/1.56      | ~ l1_struct_0(sK2)
% 7.48/1.56      | ~ v1_funct_1(sK4) ),
% 7.48/1.56      inference(instantiation,[status(thm)],[c_2412]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_9059,plain,
% 7.48/1.56      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.48/1.56      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.48/1.56      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.48/1.56      | ~ l1_struct_0(sK6)
% 7.48/1.56      | ~ l1_struct_0(sK3)
% 7.48/1.56      | ~ l1_struct_0(sK2)
% 7.48/1.56      | ~ v1_funct_1(sK4) ),
% 7.48/1.56      inference(instantiation,[status(thm)],[c_3950]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_28,negated_conjecture,
% 7.48/1.56      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.48/1.56      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.48/1.56      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.48/1.56      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.48/1.56      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.48/1.56      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.48/1.56      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.48/1.56      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.48/1.56      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.48/1.56      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.48/1.56      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 7.48/1.56      | ~ v1_funct_1(sK4) ),
% 7.48/1.56      inference(cnf_transformation,[],[f126]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_488,plain,
% 7.48/1.56      ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 7.48/1.56      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.48/1.56      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.48/1.56      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.48/1.56      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.48/1.56      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.48/1.56      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.48/1.56      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.48/1.56      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 7.48/1.56      inference(global_propositional_subsumption,
% 7.48/1.56                [status(thm)],
% 7.48/1.56                [c_28,c_69,c_68,c_67]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_489,negated_conjecture,
% 7.48/1.56      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.48/1.56      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.48/1.56      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.48/1.56      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.48/1.56      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.48/1.56      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.48/1.56      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.48/1.56      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.48/1.56      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 7.48/1.56      inference(renaming,[status(thm)],[c_488]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_2378,negated_conjecture,
% 7.48/1.56      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.48/1.56      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.48/1.56      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.48/1.56      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.48/1.56      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.48/1.56      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.48/1.56      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.48/1.56      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.48/1.56      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 7.48/1.56      inference(subtyping,[status(esa)],[c_489]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_3376,plain,
% 7.48/1.56      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.48/1.56      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.48/1.56      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.48/1.56      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.48/1.56      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.48/1.56      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.48/1.56      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.48/1.56      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 7.48/1.56      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 7.48/1.56      inference(predicate_to_equality,[status(thm)],[c_2378]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_8513,plain,
% 7.48/1.56      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.48/1.56      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.48/1.56      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.48/1.56      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.48/1.56      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.48/1.56      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.48/1.56      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.48/1.56      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.48/1.56      | l1_struct_0(sK5) != iProver_top
% 7.48/1.56      | l1_struct_0(sK3) != iProver_top
% 7.48/1.56      | l1_struct_0(sK2) != iProver_top
% 7.48/1.56      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 7.48/1.56      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top
% 7.48/1.56      | v1_funct_1(sK4) != iProver_top ),
% 7.48/1.56      inference(superposition,[status(thm)],[c_3343,c_3376]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_8961,plain,
% 7.48/1.56      ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.48/1.56      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.48/1.56      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.48/1.56      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.48/1.56      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.48/1.56      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top ),
% 7.48/1.56      inference(global_propositional_subsumption,
% 7.48/1.56                [status(thm)],
% 7.48/1.56                [c_8513,c_78,c_81,c_82,c_83,c_84,c_181,c_3984,c_4262,
% 7.48/1.56                 c_4464,c_4781,c_6178,c_6186]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_8962,plain,
% 7.48/1.56      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.48/1.56      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.48/1.56      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.48/1.56      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.48/1.56      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.48/1.56      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top ),
% 7.48/1.56      inference(renaming,[status(thm)],[c_8961]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_8963,plain,
% 7.48/1.56      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.48/1.56      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.48/1.56      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.48/1.56      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.48/1.56      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.48/1.56      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 7.48/1.56      inference(predicate_to_equality_rev,[status(thm)],[c_8962]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_6179,plain,
% 7.48/1.56      ( l1_struct_0(sK6) ),
% 7.48/1.56      inference(predicate_to_equality_rev,[status(thm)],[c_6178]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(c_180,plain,
% 7.48/1.56      ( ~ l1_pre_topc(sK3) | l1_struct_0(sK3) ),
% 7.48/1.56      inference(instantiation,[status(thm)],[c_5]) ).
% 7.48/1.56  
% 7.48/1.56  cnf(contradiction,plain,
% 7.48/1.56      ( $false ),
% 7.48/1.56      inference(minisat,
% 7.48/1.56                [status(thm)],
% 7.48/1.56                [c_30814,c_30810,c_30802,c_30798,c_17713,c_17529,c_9059,
% 7.48/1.56                 c_8963,c_6179,c_3983,c_180,c_67,c_68,c_69,c_70,c_71,
% 7.48/1.56                 c_72,c_73]) ).
% 7.48/1.56  
% 7.48/1.56  
% 7.48/1.56  % SZS output end CNFRefutation for theBenchmark.p
% 7.48/1.56  
% 7.48/1.56  ------                               Statistics
% 7.48/1.56  
% 7.48/1.56  ------ General
% 7.48/1.56  
% 7.48/1.56  abstr_ref_over_cycles:                  0
% 7.48/1.56  abstr_ref_under_cycles:                 0
% 7.48/1.56  gc_basic_clause_elim:                   0
% 7.48/1.56  forced_gc_time:                         0
% 7.48/1.56  parsing_time:                           0.017
% 7.48/1.56  unif_index_cands_time:                  0.
% 7.48/1.56  unif_index_add_time:                    0.
% 7.48/1.56  orderings_time:                         0.
% 7.48/1.56  out_proof_time:                         0.032
% 7.48/1.56  total_time:                             1.067
% 7.48/1.56  num_of_symbols:                         58
% 7.48/1.56  num_of_terms:                           29615
% 7.48/1.56  
% 7.48/1.56  ------ Preprocessing
% 7.48/1.56  
% 7.48/1.56  num_of_splits:                          0
% 7.48/1.56  num_of_split_atoms:                     0
% 7.48/1.56  num_of_reused_defs:                     0
% 7.48/1.56  num_eq_ax_congr_red:                    28
% 7.48/1.56  num_of_sem_filtered_clauses:            1
% 7.48/1.56  num_of_subtypes:                        4
% 7.48/1.56  monotx_restored_types:                  0
% 7.48/1.56  sat_num_of_epr_types:                   0
% 7.48/1.56  sat_num_of_non_cyclic_types:            0
% 7.48/1.56  sat_guarded_non_collapsed_types:        1
% 7.48/1.56  num_pure_diseq_elim:                    0
% 7.48/1.56  simp_replaced_by:                       0
% 7.48/1.56  res_preprocessed:                       244
% 7.48/1.56  prep_upred:                             0
% 7.48/1.56  prep_unflattend:                        148
% 7.48/1.56  smt_new_axioms:                         0
% 7.48/1.56  pred_elim_cands:                        11
% 7.48/1.56  pred_elim:                              3
% 7.48/1.56  pred_elim_cl:                           3
% 7.48/1.56  pred_elim_cycles:                       5
% 7.48/1.56  merged_defs:                            0
% 7.48/1.56  merged_defs_ncl:                        0
% 7.48/1.56  bin_hyper_res:                          0
% 7.48/1.56  prep_cycles:                            4
% 7.48/1.56  pred_elim_time:                         0.062
% 7.48/1.56  splitting_time:                         0.
% 7.48/1.56  sem_filter_time:                        0.
% 7.48/1.56  monotx_time:                            0.
% 7.48/1.56  subtype_inf_time:                       0.001
% 7.48/1.56  
% 7.48/1.56  ------ Problem properties
% 7.48/1.56  
% 7.48/1.56  clauses:                                49
% 7.48/1.56  conjectures:                            23
% 7.48/1.56  epr:                                    13
% 7.48/1.56  horn:                                   33
% 7.48/1.56  ground:                                 23
% 7.48/1.56  unary:                                  15
% 7.48/1.56  binary:                                 17
% 7.48/1.56  lits:                                   168
% 7.48/1.56  lits_eq:                                4
% 7.48/1.56  fd_pure:                                0
% 7.48/1.56  fd_pseudo:                              0
% 7.48/1.56  fd_cond:                                0
% 7.48/1.56  fd_pseudo_cond:                         0
% 7.48/1.56  ac_symbols:                             0
% 7.48/1.56  
% 7.48/1.56  ------ Propositional Solver
% 7.48/1.56  
% 7.48/1.56  prop_solver_calls:                      32
% 7.48/1.56  prop_fast_solver_calls:                 3886
% 7.48/1.56  smt_solver_calls:                       0
% 7.48/1.56  smt_fast_solver_calls:                  0
% 7.48/1.56  prop_num_of_clauses:                    10376
% 7.48/1.56  prop_preprocess_simplified:             22071
% 7.48/1.56  prop_fo_subsumed:                       426
% 7.48/1.56  prop_solver_time:                       0.
% 7.48/1.56  smt_solver_time:                        0.
% 7.48/1.56  smt_fast_solver_time:                   0.
% 7.48/1.56  prop_fast_solver_time:                  0.
% 7.48/1.56  prop_unsat_core_time:                   0.001
% 7.48/1.56  
% 7.48/1.56  ------ QBF
% 7.48/1.56  
% 7.48/1.56  qbf_q_res:                              0
% 7.48/1.56  qbf_num_tautologies:                    0
% 7.48/1.56  qbf_prep_cycles:                        0
% 7.48/1.56  
% 7.48/1.56  ------ BMC1
% 7.48/1.56  
% 7.48/1.56  bmc1_current_bound:                     -1
% 7.48/1.56  bmc1_last_solved_bound:                 -1
% 7.48/1.56  bmc1_unsat_core_size:                   -1
% 7.48/1.56  bmc1_unsat_core_parents_size:           -1
% 7.48/1.56  bmc1_merge_next_fun:                    0
% 7.48/1.56  bmc1_unsat_core_clauses_time:           0.
% 7.48/1.56  
% 7.48/1.56  ------ Instantiation
% 7.48/1.56  
% 7.48/1.56  inst_num_of_clauses:                    2589
% 7.48/1.56  inst_num_in_passive:                    1280
% 7.48/1.56  inst_num_in_active:                     1168
% 7.48/1.56  inst_num_in_unprocessed:                140
% 7.48/1.56  inst_num_of_loops:                      1218
% 7.48/1.56  inst_num_of_learning_restarts:          0
% 7.48/1.56  inst_num_moves_active_passive:          46
% 7.48/1.56  inst_lit_activity:                      0
% 7.48/1.56  inst_lit_activity_moves:                2
% 7.48/1.56  inst_num_tautologies:                   0
% 7.48/1.56  inst_num_prop_implied:                  0
% 7.48/1.56  inst_num_existing_simplified:           0
% 7.48/1.56  inst_num_eq_res_simplified:             0
% 7.48/1.56  inst_num_child_elim:                    0
% 7.48/1.56  inst_num_of_dismatching_blockings:      1849
% 7.48/1.56  inst_num_of_non_proper_insts:           2652
% 7.48/1.56  inst_num_of_duplicates:                 0
% 7.48/1.56  inst_inst_num_from_inst_to_res:         0
% 7.48/1.56  inst_dismatching_checking_time:         0.
% 7.48/1.56  
% 7.48/1.56  ------ Resolution
% 7.48/1.56  
% 7.48/1.56  res_num_of_clauses:                     0
% 7.48/1.56  res_num_in_passive:                     0
% 7.48/1.56  res_num_in_active:                      0
% 7.48/1.56  res_num_of_loops:                       248
% 7.48/1.56  res_forward_subset_subsumed:            19
% 7.48/1.56  res_backward_subset_subsumed:           0
% 7.48/1.56  res_forward_subsumed:                   0
% 7.48/1.56  res_backward_subsumed:                  0
% 7.48/1.56  res_forward_subsumption_resolution:     0
% 7.48/1.56  res_backward_subsumption_resolution:    0
% 7.48/1.56  res_clause_to_clause_subsumption:       2531
% 7.48/1.56  res_orphan_elimination:                 0
% 7.48/1.56  res_tautology_del:                      77
% 7.48/1.56  res_num_eq_res_simplified:              0
% 7.48/1.56  res_num_sel_changes:                    0
% 7.48/1.56  res_moves_from_active_to_pass:          0
% 7.48/1.56  
% 7.48/1.56  ------ Superposition
% 7.48/1.56  
% 7.48/1.56  sup_time_total:                         0.
% 7.48/1.56  sup_time_generating:                    0.
% 7.48/1.56  sup_time_sim_full:                      0.
% 7.48/1.56  sup_time_sim_immed:                     0.
% 7.48/1.56  
% 7.48/1.56  sup_num_of_clauses:                     563
% 7.48/1.56  sup_num_in_active:                      206
% 7.48/1.56  sup_num_in_passive:                     357
% 7.48/1.56  sup_num_of_loops:                       242
% 7.48/1.56  sup_fw_superposition:                   257
% 7.48/1.56  sup_bw_superposition:                   476
% 7.48/1.56  sup_immediate_simplified:               277
% 7.48/1.56  sup_given_eliminated:                   0
% 7.48/1.56  comparisons_done:                       0
% 7.48/1.56  comparisons_avoided:                    0
% 7.48/1.56  
% 7.48/1.56  ------ Simplifications
% 7.48/1.56  
% 7.48/1.56  
% 7.48/1.56  sim_fw_subset_subsumed:                 84
% 7.48/1.56  sim_bw_subset_subsumed:                 16
% 7.48/1.56  sim_fw_subsumed:                        23
% 7.48/1.56  sim_bw_subsumed:                        5
% 7.48/1.56  sim_fw_subsumption_res:                 17
% 7.48/1.56  sim_bw_subsumption_res:                 0
% 7.48/1.56  sim_tautology_del:                      15
% 7.48/1.56  sim_eq_tautology_del:                   14
% 7.48/1.56  sim_eq_res_simp:                        0
% 7.48/1.56  sim_fw_demodulated:                     6
% 7.48/1.56  sim_bw_demodulated:                     33
% 7.48/1.56  sim_light_normalised:                   186
% 7.48/1.56  sim_joinable_taut:                      0
% 7.48/1.56  sim_joinable_simp:                      0
% 7.48/1.56  sim_ac_normalised:                      0
% 7.48/1.56  sim_smt_subsumption:                    0
% 7.48/1.56  
%------------------------------------------------------------------------------
