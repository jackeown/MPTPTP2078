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
% DateTime   : Thu Dec  3 12:24:19 EST 2020

% Result     : Theorem 23.02s
% Output     : CNFRefutation 23.02s
% Verified   : 
% Statistics : Number of formulae       :  292 (4027 expanded)
%              Number of clauses        :  191 ( 837 expanded)
%              Number of leaves         :   21 (1403 expanded)
%              Depth                    :   25
%              Number of atoms          : 1880 (123784 expanded)
%              Number of equality atoms :  480 (4747 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   78 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41,plain,(
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

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f93,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f16,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f60,plain,(
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

fof(f59,plain,(
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

fof(f58,plain,(
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

fof(f57,plain,(
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

fof(f56,plain,
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

fof(f61,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f55,f60,f59,f58,f57,f56])).

fof(f111,plain,(
    k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f61])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f98,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f100,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f107,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f108,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f109,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f110,plain,(
    m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f106,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f61])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f104,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f99,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f101,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f102,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f103,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f105,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f61])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
      <=> sP0(X1,X3,X4,X0,X2) )
      | ~ sP1(X2,X0,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0)
      | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
      | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
      | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f43,plain,(
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
    inference(definition_folding,[],[f38,f42,f41])).

fof(f97,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f112,plain,(
    r4_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f143,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f96,plain,(
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
    inference(cnf_transformation,[],[f53])).

fof(f135,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f139,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f75,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f76,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f127,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f119,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f123,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f145,plain,
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
    inference(cnf_transformation,[],[f61])).

cnf(c_32,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_74463,plain,
    ( ~ sP0(X0,sK6,sK4,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,X0,sK4,sK5),sK5,X0) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_74495,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
    inference(instantiation,[status(thm)],[c_74463])).

cnf(c_29,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_74465,plain,
    ( ~ sP0(X0,sK6,sK4,sK2,sK5)
    | v1_funct_2(k2_tmap_1(sK2,X0,sK4,sK6),u1_struct_0(sK6),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_74487,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_74465])).

cnf(c_28,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_74466,plain,
    ( ~ sP0(X0,sK6,sK4,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,X0,sK4,sK6),sK6,X0) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_74483,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
    inference(instantiation,[status(thm)],[c_74466])).

cnf(c_70,negated_conjecture,
    ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_4048,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10071,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_70,c_4048])).

cnf(c_83,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_84,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_83])).

cnf(c_81,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_86,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_81])).

cnf(c_74,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_93,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_74])).

cnf(c_73,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_94,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_72,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_95,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_72])).

cnf(c_71,negated_conjecture,
    ( m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_96,plain,
    ( m1_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_10219,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10071,c_84,c_86,c_93,c_94,c_95,c_96])).

cnf(c_75,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_4022,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_75])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f77])).

cnf(c_4049,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_11460,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0)) = k2_tmap_1(sK2,sK3,sK4,X0)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4022,c_4049])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4052,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9271,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k7_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4022,c_4052])).

cnf(c_77,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_4635,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_4796,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_4635])).

cnf(c_9408,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9271,c_77,c_75,c_4796])).

cnf(c_11500,plain,
    ( k2_tmap_1(sK2,sK3,sK4,X0) = k7_relat_1(sK4,u1_struct_0(X0))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11460,c_9408])).

cnf(c_82,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_85,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_82])).

cnf(c_80,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_87,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_80])).

cnf(c_79,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_88,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_79])).

cnf(c_78,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_89,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_78])).

cnf(c_90,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_77])).

cnf(c_76,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_91,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_76])).

cnf(c_26259,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | k2_tmap_1(sK2,sK3,sK4,X0) = k7_relat_1(sK4,u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11500,c_84,c_85,c_86,c_87,c_88,c_89,c_90,c_91])).

cnf(c_26260,plain,
    ( k2_tmap_1(sK2,sK3,sK4,X0) = k7_relat_1(sK4,u1_struct_0(X0))
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_26259])).

cnf(c_26270,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_10219,c_26260])).

cnf(c_11,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_967,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_11,c_8])).

cnf(c_4011,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_967])).

cnf(c_4742,plain,
    ( r1_tarski(k1_relat_1(sK4),u1_struct_0(sK2)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4022,c_4011])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4055,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5270,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4022,c_4055])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_652,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_653,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_652])).

cnf(c_772,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_653])).

cnf(c_4703,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_5593,plain,
    ( ~ r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4703])).

cnf(c_5594,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5593])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_6786,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_6787,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6786])).

cnf(c_7038,plain,
    ( r1_tarski(k1_relat_1(sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4742,c_5270,c_5594,c_6787])).

cnf(c_10,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_4053,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8221,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7038,c_4053])).

cnf(c_12157,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8221,c_5270,c_5594,c_6787])).

cnf(c_26272,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_26270,c_12157])).

cnf(c_25,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | sP0(X4,X3,X2,X1,X0)
    | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
    | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
    | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
    | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_35,plain,
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
    inference(cnf_transformation,[],[f97])).

cnf(c_69,negated_conjecture,
    ( r4_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_986,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
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
    inference(resolution_lifted,[status(thm)],[c_35,c_69])).

cnf(c_987,plain,
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
    inference(unflattening,[status(thm)],[c_986])).

cnf(c_991,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | sP1(sK5,sK2,X0,sK6,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_987,c_83,c_82,c_81,c_74,c_73,c_72,c_71])).

cnf(c_992,plain,
    ( sP1(sK5,sK2,X0,sK6,X1)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_991])).

cnf(c_1027,plain,
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
    inference(resolution_lifted,[status(thm)],[c_25,c_992])).

cnf(c_1028,plain,
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
    inference(unflattening,[status(thm)],[c_1027])).

cnf(c_4010,plain,
    ( sP0(X0,sK6,X1,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0) != iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1028])).

cnf(c_4406,plain,
    ( sP0(X0,sK6,X1,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0,X1,sK2),sK2,X0) != iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0,X1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4010,c_70])).

cnf(c_28264,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_26272,c_4406])).

cnf(c_28328,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28264,c_26272])).

cnf(c_28449,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_28328])).

cnf(c_21,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1156,plain,
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
    inference(resolution_lifted,[status(thm)],[c_21,c_992])).

cnf(c_1157,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_1156])).

cnf(c_4006,plain,
    ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0)))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1157])).

cnf(c_4331,plain,
    ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4006,c_70])).

cnf(c_38,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_4034,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_26,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_4043,plain,
    ( sP0(X0,X1,X2,X3,X4) = iProver_top
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) != iProver_top
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) != iProver_top
    | v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) != iProver_top
    | v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9966,plain,
    ( sP0(sK3,X0,sK4,sK2,sK6) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4034,c_4043])).

cnf(c_92,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_75])).

cnf(c_46,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_120,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_42,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_124,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_13,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_187,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_189,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_187])).

cnf(c_5058,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_5059,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5058])).

cnf(c_4026,plain,
    ( m1_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_4050,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6518,plain,
    ( l1_pre_topc(sK6) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4026,c_4050])).

cnf(c_6815,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6518,c_86])).

cnf(c_4051,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6820,plain,
    ( l1_struct_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_6815,c_4051])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4679,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X2)
    | v1_funct_1(k2_tmap_1(X0,X1,sK4,X2))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_4819,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4679])).

cnf(c_7586,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK6)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4819])).

cnf(c_7587,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7586])).

cnf(c_10542,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
    | sP0(sK3,X0,sK4,sK2,sK6) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9966,c_86,c_89,c_90,c_91,c_92,c_120,c_124,c_189,c_5059,c_6820,c_7587])).

cnf(c_10543,plain,
    ( sP0(sK3,X0,sK4,sK2,sK6) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10542])).

cnf(c_10557,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | sP0(sK3,sK2,sK4,sK2,sK6) = iProver_top
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
    inference(superposition,[status(thm)],[c_4331,c_10543])).

cnf(c_22,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1126,plain,
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
    inference(resolution_lifted,[status(thm)],[c_22,c_992])).

cnf(c_1127,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_1126])).

cnf(c_4007,plain,
    ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0) = iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1127])).

cnf(c_4297,plain,
    ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0,X1,sK2),sK2,X0) = iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4007,c_70])).

cnf(c_5463,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4022,c_4297])).

cnf(c_8969,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
    | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5463,c_87,c_88,c_89,c_90,c_91])).

cnf(c_8970,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_8969])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_4689,plain,
    ( v1_funct_2(k2_tmap_1(X0,X1,sK4,X2),u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_4829,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4689])).

cnf(c_10842,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4829])).

cnf(c_10845,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10842])).

cnf(c_54,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_4030,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_9967,plain,
    ( sP0(sK3,X0,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4030,c_4043])).

cnf(c_62,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_104,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_58,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_108,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_5894,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4819])).

cnf(c_5895,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5894])).

cnf(c_4024,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_6519,plain,
    ( l1_pre_topc(sK5) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4024,c_4050])).

cnf(c_7030,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6519,c_86])).

cnf(c_7035,plain,
    ( l1_struct_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_7030,c_4051])).

cnf(c_10692,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
    | sP0(sK3,X0,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9967,c_86,c_89,c_90,c_91,c_92,c_104,c_108,c_189,c_5059,c_5895,c_7035])).

cnf(c_10693,plain,
    ( sP0(sK3,X0,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10692])).

cnf(c_10705,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4034,c_10693])).

cnf(c_11011,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10705,c_86,c_89,c_90,c_91,c_92,c_120,c_124,c_189,c_5059,c_6820,c_7587])).

cnf(c_24,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1066,plain,
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
    inference(resolution_lifted,[status(thm)],[c_24,c_992])).

cnf(c_1067,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X1)
    | v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(unflattening,[status(thm)],[c_1066])).

cnf(c_4009,plain,
    ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1067])).

cnf(c_4280,plain,
    ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0,X1,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4009,c_70])).

cnf(c_5452,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4022,c_4280])).

cnf(c_8962,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top
    | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5452,c_87,c_88,c_89,c_90,c_91])).

cnf(c_8963,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8962])).

cnf(c_11026,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11011,c_8963])).

cnf(c_11904,plain,
    ( sP0(sK3,sK2,sK4,sK2,sK6) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10557,c_86,c_87,c_88,c_89,c_90,c_91,c_92,c_189,c_5059,c_8970,c_10845,c_11011,c_11026])).

cnf(c_4041,plain,
    ( sP0(X0,X1,X2,X3,X4) != iProver_top
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_11913,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_11904,c_4041])).

cnf(c_28219,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_26272,c_11913])).

cnf(c_28246,plain,
    ( v5_pre_topc(sK4,sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_28219])).

cnf(c_4045,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | l1_struct_0(X3) != iProver_top
    | l1_struct_0(X2) != iProver_top
    | l1_struct_0(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4056,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_4046,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) = iProver_top
    | l1_struct_0(X3) != iProver_top
    | l1_struct_0(X2) != iProver_top
    | l1_struct_0(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_36,negated_conjecture,
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
    inference(cnf_transformation,[],[f145])).

cnf(c_532,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_36,c_77,c_76,c_75])).

cnf(c_533,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(renaming,[status(thm)],[c_532])).

cnf(c_4013,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_533])).

cnf(c_11053,plain,
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
    inference(superposition,[status(thm)],[c_4046,c_4013])).

cnf(c_11657,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11053,c_86,c_89,c_90,c_91,c_92,c_189,c_5059,c_5895,c_6820,c_7035,c_7587])).

cnf(c_11658,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11657])).

cnf(c_11667,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(k2_tmap_1(sK2,sK3,sK4,sK6),k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4056,c_11658])).

cnf(c_11668,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4046,c_11658])).

cnf(c_13416,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11667,c_86,c_89,c_90,c_91,c_92,c_189,c_5059,c_6820,c_11668])).

cnf(c_13417,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13416])).

cnf(c_13425,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4045,c_13417])).

cnf(c_13447,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13425])).

cnf(c_7036,plain,
    ( l1_struct_0(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7035])).

cnf(c_188,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_74495,c_74487,c_74483,c_28449,c_28246,c_13447,c_7036,c_5058,c_188,c_75,c_76,c_77,c_78,c_79,c_80,c_81])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:16:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 23.02/3.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.02/3.51  
% 23.02/3.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.02/3.51  
% 23.02/3.51  ------  iProver source info
% 23.02/3.51  
% 23.02/3.51  git: date: 2020-06-30 10:37:57 +0100
% 23.02/3.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.02/3.51  git: non_committed_changes: false
% 23.02/3.51  git: last_make_outside_of_git: false
% 23.02/3.51  
% 23.02/3.51  ------ 
% 23.02/3.51  
% 23.02/3.51  ------ Input Options
% 23.02/3.51  
% 23.02/3.51  --out_options                           all
% 23.02/3.51  --tptp_safe_out                         true
% 23.02/3.51  --problem_path                          ""
% 23.02/3.51  --include_path                          ""
% 23.02/3.51  --clausifier                            res/vclausify_rel
% 23.02/3.51  --clausifier_options                    --mode clausify
% 23.02/3.51  --stdin                                 false
% 23.02/3.51  --stats_out                             all
% 23.02/3.51  
% 23.02/3.51  ------ General Options
% 23.02/3.51  
% 23.02/3.51  --fof                                   false
% 23.02/3.51  --time_out_real                         305.
% 23.02/3.51  --time_out_virtual                      -1.
% 23.02/3.51  --symbol_type_check                     false
% 23.02/3.51  --clausify_out                          false
% 23.02/3.51  --sig_cnt_out                           false
% 23.02/3.51  --trig_cnt_out                          false
% 23.02/3.51  --trig_cnt_out_tolerance                1.
% 23.02/3.51  --trig_cnt_out_sk_spl                   false
% 23.02/3.51  --abstr_cl_out                          false
% 23.02/3.51  
% 23.02/3.51  ------ Global Options
% 23.02/3.51  
% 23.02/3.51  --schedule                              default
% 23.02/3.51  --add_important_lit                     false
% 23.02/3.51  --prop_solver_per_cl                    1000
% 23.02/3.51  --min_unsat_core                        false
% 23.02/3.51  --soft_assumptions                      false
% 23.02/3.51  --soft_lemma_size                       3
% 23.02/3.51  --prop_impl_unit_size                   0
% 23.02/3.51  --prop_impl_unit                        []
% 23.02/3.51  --share_sel_clauses                     true
% 23.02/3.51  --reset_solvers                         false
% 23.02/3.51  --bc_imp_inh                            [conj_cone]
% 23.02/3.51  --conj_cone_tolerance                   3.
% 23.02/3.51  --extra_neg_conj                        none
% 23.02/3.51  --large_theory_mode                     true
% 23.02/3.51  --prolific_symb_bound                   200
% 23.02/3.51  --lt_threshold                          2000
% 23.02/3.51  --clause_weak_htbl                      true
% 23.02/3.51  --gc_record_bc_elim                     false
% 23.02/3.51  
% 23.02/3.51  ------ Preprocessing Options
% 23.02/3.51  
% 23.02/3.51  --preprocessing_flag                    true
% 23.02/3.51  --time_out_prep_mult                    0.1
% 23.02/3.51  --splitting_mode                        input
% 23.02/3.51  --splitting_grd                         true
% 23.02/3.51  --splitting_cvd                         false
% 23.02/3.51  --splitting_cvd_svl                     false
% 23.02/3.51  --splitting_nvd                         32
% 23.02/3.51  --sub_typing                            true
% 23.02/3.51  --prep_gs_sim                           true
% 23.02/3.51  --prep_unflatten                        true
% 23.02/3.51  --prep_res_sim                          true
% 23.02/3.51  --prep_upred                            true
% 23.02/3.51  --prep_sem_filter                       exhaustive
% 23.02/3.51  --prep_sem_filter_out                   false
% 23.02/3.51  --pred_elim                             true
% 23.02/3.51  --res_sim_input                         true
% 23.02/3.51  --eq_ax_congr_red                       true
% 23.02/3.51  --pure_diseq_elim                       true
% 23.02/3.51  --brand_transform                       false
% 23.02/3.51  --non_eq_to_eq                          false
% 23.02/3.51  --prep_def_merge                        true
% 23.02/3.51  --prep_def_merge_prop_impl              false
% 23.02/3.51  --prep_def_merge_mbd                    true
% 23.02/3.51  --prep_def_merge_tr_red                 false
% 23.02/3.51  --prep_def_merge_tr_cl                  false
% 23.02/3.51  --smt_preprocessing                     true
% 23.02/3.51  --smt_ac_axioms                         fast
% 23.02/3.51  --preprocessed_out                      false
% 23.02/3.51  --preprocessed_stats                    false
% 23.02/3.51  
% 23.02/3.51  ------ Abstraction refinement Options
% 23.02/3.51  
% 23.02/3.51  --abstr_ref                             []
% 23.02/3.51  --abstr_ref_prep                        false
% 23.02/3.51  --abstr_ref_until_sat                   false
% 23.02/3.51  --abstr_ref_sig_restrict                funpre
% 23.02/3.51  --abstr_ref_af_restrict_to_split_sk     false
% 23.02/3.51  --abstr_ref_under                       []
% 23.02/3.51  
% 23.02/3.51  ------ SAT Options
% 23.02/3.51  
% 23.02/3.51  --sat_mode                              false
% 23.02/3.51  --sat_fm_restart_options                ""
% 23.02/3.51  --sat_gr_def                            false
% 23.02/3.51  --sat_epr_types                         true
% 23.02/3.51  --sat_non_cyclic_types                  false
% 23.02/3.51  --sat_finite_models                     false
% 23.02/3.51  --sat_fm_lemmas                         false
% 23.02/3.51  --sat_fm_prep                           false
% 23.02/3.51  --sat_fm_uc_incr                        true
% 23.02/3.51  --sat_out_model                         small
% 23.02/3.51  --sat_out_clauses                       false
% 23.02/3.51  
% 23.02/3.51  ------ QBF Options
% 23.02/3.51  
% 23.02/3.51  --qbf_mode                              false
% 23.02/3.51  --qbf_elim_univ                         false
% 23.02/3.51  --qbf_dom_inst                          none
% 23.02/3.51  --qbf_dom_pre_inst                      false
% 23.02/3.51  --qbf_sk_in                             false
% 23.02/3.51  --qbf_pred_elim                         true
% 23.02/3.51  --qbf_split                             512
% 23.02/3.51  
% 23.02/3.51  ------ BMC1 Options
% 23.02/3.51  
% 23.02/3.51  --bmc1_incremental                      false
% 23.02/3.51  --bmc1_axioms                           reachable_all
% 23.02/3.51  --bmc1_min_bound                        0
% 23.02/3.51  --bmc1_max_bound                        -1
% 23.02/3.51  --bmc1_max_bound_default                -1
% 23.02/3.51  --bmc1_symbol_reachability              true
% 23.02/3.51  --bmc1_property_lemmas                  false
% 23.02/3.51  --bmc1_k_induction                      false
% 23.02/3.51  --bmc1_non_equiv_states                 false
% 23.02/3.51  --bmc1_deadlock                         false
% 23.02/3.51  --bmc1_ucm                              false
% 23.02/3.51  --bmc1_add_unsat_core                   none
% 23.02/3.51  --bmc1_unsat_core_children              false
% 23.02/3.51  --bmc1_unsat_core_extrapolate_axioms    false
% 23.02/3.51  --bmc1_out_stat                         full
% 23.02/3.51  --bmc1_ground_init                      false
% 23.02/3.51  --bmc1_pre_inst_next_state              false
% 23.02/3.51  --bmc1_pre_inst_state                   false
% 23.02/3.51  --bmc1_pre_inst_reach_state             false
% 23.02/3.51  --bmc1_out_unsat_core                   false
% 23.02/3.51  --bmc1_aig_witness_out                  false
% 23.02/3.51  --bmc1_verbose                          false
% 23.02/3.51  --bmc1_dump_clauses_tptp                false
% 23.02/3.51  --bmc1_dump_unsat_core_tptp             false
% 23.02/3.51  --bmc1_dump_file                        -
% 23.02/3.51  --bmc1_ucm_expand_uc_limit              128
% 23.02/3.51  --bmc1_ucm_n_expand_iterations          6
% 23.02/3.51  --bmc1_ucm_extend_mode                  1
% 23.02/3.51  --bmc1_ucm_init_mode                    2
% 23.02/3.51  --bmc1_ucm_cone_mode                    none
% 23.02/3.51  --bmc1_ucm_reduced_relation_type        0
% 23.02/3.51  --bmc1_ucm_relax_model                  4
% 23.02/3.51  --bmc1_ucm_full_tr_after_sat            true
% 23.02/3.51  --bmc1_ucm_expand_neg_assumptions       false
% 23.02/3.51  --bmc1_ucm_layered_model                none
% 23.02/3.51  --bmc1_ucm_max_lemma_size               10
% 23.02/3.51  
% 23.02/3.51  ------ AIG Options
% 23.02/3.51  
% 23.02/3.51  --aig_mode                              false
% 23.02/3.51  
% 23.02/3.51  ------ Instantiation Options
% 23.02/3.51  
% 23.02/3.51  --instantiation_flag                    true
% 23.02/3.51  --inst_sos_flag                         false
% 23.02/3.51  --inst_sos_phase                        true
% 23.02/3.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.02/3.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.02/3.51  --inst_lit_sel_side                     num_symb
% 23.02/3.51  --inst_solver_per_active                1400
% 23.02/3.51  --inst_solver_calls_frac                1.
% 23.02/3.51  --inst_passive_queue_type               priority_queues
% 23.02/3.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.02/3.51  --inst_passive_queues_freq              [25;2]
% 23.02/3.51  --inst_dismatching                      true
% 23.02/3.51  --inst_eager_unprocessed_to_passive     true
% 23.02/3.51  --inst_prop_sim_given                   true
% 23.02/3.51  --inst_prop_sim_new                     false
% 23.02/3.51  --inst_subs_new                         false
% 23.02/3.51  --inst_eq_res_simp                      false
% 23.02/3.51  --inst_subs_given                       false
% 23.02/3.51  --inst_orphan_elimination               true
% 23.02/3.51  --inst_learning_loop_flag               true
% 23.02/3.51  --inst_learning_start                   3000
% 23.02/3.51  --inst_learning_factor                  2
% 23.02/3.51  --inst_start_prop_sim_after_learn       3
% 23.02/3.51  --inst_sel_renew                        solver
% 23.02/3.51  --inst_lit_activity_flag                true
% 23.02/3.51  --inst_restr_to_given                   false
% 23.02/3.51  --inst_activity_threshold               500
% 23.02/3.51  --inst_out_proof                        true
% 23.02/3.51  
% 23.02/3.51  ------ Resolution Options
% 23.02/3.51  
% 23.02/3.51  --resolution_flag                       true
% 23.02/3.51  --res_lit_sel                           adaptive
% 23.02/3.51  --res_lit_sel_side                      none
% 23.02/3.51  --res_ordering                          kbo
% 23.02/3.51  --res_to_prop_solver                    active
% 23.02/3.51  --res_prop_simpl_new                    false
% 23.02/3.51  --res_prop_simpl_given                  true
% 23.02/3.51  --res_passive_queue_type                priority_queues
% 23.02/3.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.02/3.51  --res_passive_queues_freq               [15;5]
% 23.02/3.51  --res_forward_subs                      full
% 23.02/3.51  --res_backward_subs                     full
% 23.02/3.51  --res_forward_subs_resolution           true
% 23.02/3.51  --res_backward_subs_resolution          true
% 23.02/3.51  --res_orphan_elimination                true
% 23.02/3.51  --res_time_limit                        2.
% 23.02/3.51  --res_out_proof                         true
% 23.02/3.51  
% 23.02/3.51  ------ Superposition Options
% 23.02/3.51  
% 23.02/3.51  --superposition_flag                    true
% 23.02/3.51  --sup_passive_queue_type                priority_queues
% 23.02/3.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.02/3.51  --sup_passive_queues_freq               [8;1;4]
% 23.02/3.51  --demod_completeness_check              fast
% 23.02/3.51  --demod_use_ground                      true
% 23.02/3.51  --sup_to_prop_solver                    passive
% 23.02/3.51  --sup_prop_simpl_new                    true
% 23.02/3.51  --sup_prop_simpl_given                  true
% 23.02/3.51  --sup_fun_splitting                     false
% 23.02/3.51  --sup_smt_interval                      50000
% 23.02/3.51  
% 23.02/3.51  ------ Superposition Simplification Setup
% 23.02/3.51  
% 23.02/3.51  --sup_indices_passive                   []
% 23.02/3.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.02/3.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.02/3.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.02/3.51  --sup_full_triv                         [TrivRules;PropSubs]
% 23.02/3.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.02/3.51  --sup_full_bw                           [BwDemod]
% 23.02/3.51  --sup_immed_triv                        [TrivRules]
% 23.02/3.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.02/3.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.02/3.51  --sup_immed_bw_main                     []
% 23.02/3.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.02/3.51  --sup_input_triv                        [Unflattening;TrivRules]
% 23.02/3.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.02/3.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.02/3.51  
% 23.02/3.51  ------ Combination Options
% 23.02/3.51  
% 23.02/3.51  --comb_res_mult                         3
% 23.02/3.51  --comb_sup_mult                         2
% 23.02/3.51  --comb_inst_mult                        10
% 23.02/3.51  
% 23.02/3.51  ------ Debug Options
% 23.02/3.51  
% 23.02/3.51  --dbg_backtrace                         false
% 23.02/3.51  --dbg_dump_prop_clauses                 false
% 23.02/3.51  --dbg_dump_prop_clauses_file            -
% 23.02/3.51  --dbg_out_stat                          false
% 23.02/3.51  ------ Parsing...
% 23.02/3.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.02/3.51  
% 23.02/3.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 23.02/3.51  
% 23.02/3.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.02/3.51  
% 23.02/3.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.02/3.51  ------ Proving...
% 23.02/3.51  ------ Problem Properties 
% 23.02/3.51  
% 23.02/3.51  
% 23.02/3.51  clauses                                 55
% 23.02/3.51  conjectures                             23
% 23.02/3.51  EPR                                     17
% 23.02/3.51  Horn                                    39
% 23.02/3.51  unary                                   16
% 23.02/3.51  binary                                  19
% 23.02/3.51  lits                                    182
% 23.02/3.51  lits eq                                 5
% 23.02/3.51  fd_pure                                 0
% 23.02/3.51  fd_pseudo                               0
% 23.02/3.51  fd_cond                                 0
% 23.02/3.51  fd_pseudo_cond                          1
% 23.02/3.51  AC symbols                              0
% 23.02/3.51  
% 23.02/3.51  ------ Schedule dynamic 5 is on 
% 23.02/3.51  
% 23.02/3.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.02/3.51  
% 23.02/3.51  
% 23.02/3.51  ------ 
% 23.02/3.51  Current options:
% 23.02/3.51  ------ 
% 23.02/3.51  
% 23.02/3.51  ------ Input Options
% 23.02/3.51  
% 23.02/3.51  --out_options                           all
% 23.02/3.51  --tptp_safe_out                         true
% 23.02/3.51  --problem_path                          ""
% 23.02/3.51  --include_path                          ""
% 23.02/3.51  --clausifier                            res/vclausify_rel
% 23.02/3.51  --clausifier_options                    --mode clausify
% 23.02/3.51  --stdin                                 false
% 23.02/3.51  --stats_out                             all
% 23.02/3.51  
% 23.02/3.51  ------ General Options
% 23.02/3.51  
% 23.02/3.51  --fof                                   false
% 23.02/3.51  --time_out_real                         305.
% 23.02/3.51  --time_out_virtual                      -1.
% 23.02/3.51  --symbol_type_check                     false
% 23.02/3.51  --clausify_out                          false
% 23.02/3.51  --sig_cnt_out                           false
% 23.02/3.51  --trig_cnt_out                          false
% 23.02/3.51  --trig_cnt_out_tolerance                1.
% 23.02/3.51  --trig_cnt_out_sk_spl                   false
% 23.02/3.51  --abstr_cl_out                          false
% 23.02/3.51  
% 23.02/3.51  ------ Global Options
% 23.02/3.51  
% 23.02/3.51  --schedule                              default
% 23.02/3.51  --add_important_lit                     false
% 23.02/3.51  --prop_solver_per_cl                    1000
% 23.02/3.51  --min_unsat_core                        false
% 23.02/3.51  --soft_assumptions                      false
% 23.02/3.51  --soft_lemma_size                       3
% 23.02/3.51  --prop_impl_unit_size                   0
% 23.02/3.51  --prop_impl_unit                        []
% 23.02/3.51  --share_sel_clauses                     true
% 23.02/3.51  --reset_solvers                         false
% 23.02/3.51  --bc_imp_inh                            [conj_cone]
% 23.02/3.51  --conj_cone_tolerance                   3.
% 23.02/3.51  --extra_neg_conj                        none
% 23.02/3.51  --large_theory_mode                     true
% 23.02/3.51  --prolific_symb_bound                   200
% 23.02/3.51  --lt_threshold                          2000
% 23.02/3.51  --clause_weak_htbl                      true
% 23.02/3.51  --gc_record_bc_elim                     false
% 23.02/3.51  
% 23.02/3.51  ------ Preprocessing Options
% 23.02/3.51  
% 23.02/3.51  --preprocessing_flag                    true
% 23.02/3.51  --time_out_prep_mult                    0.1
% 23.02/3.51  --splitting_mode                        input
% 23.02/3.51  --splitting_grd                         true
% 23.02/3.51  --splitting_cvd                         false
% 23.02/3.51  --splitting_cvd_svl                     false
% 23.02/3.51  --splitting_nvd                         32
% 23.02/3.51  --sub_typing                            true
% 23.02/3.51  --prep_gs_sim                           true
% 23.02/3.51  --prep_unflatten                        true
% 23.02/3.51  --prep_res_sim                          true
% 23.02/3.51  --prep_upred                            true
% 23.02/3.51  --prep_sem_filter                       exhaustive
% 23.02/3.51  --prep_sem_filter_out                   false
% 23.02/3.51  --pred_elim                             true
% 23.02/3.51  --res_sim_input                         true
% 23.02/3.51  --eq_ax_congr_red                       true
% 23.02/3.51  --pure_diseq_elim                       true
% 23.02/3.51  --brand_transform                       false
% 23.02/3.51  --non_eq_to_eq                          false
% 23.02/3.51  --prep_def_merge                        true
% 23.02/3.51  --prep_def_merge_prop_impl              false
% 23.02/3.51  --prep_def_merge_mbd                    true
% 23.02/3.51  --prep_def_merge_tr_red                 false
% 23.02/3.51  --prep_def_merge_tr_cl                  false
% 23.02/3.51  --smt_preprocessing                     true
% 23.02/3.51  --smt_ac_axioms                         fast
% 23.02/3.51  --preprocessed_out                      false
% 23.02/3.51  --preprocessed_stats                    false
% 23.02/3.51  
% 23.02/3.51  ------ Abstraction refinement Options
% 23.02/3.51  
% 23.02/3.51  --abstr_ref                             []
% 23.02/3.51  --abstr_ref_prep                        false
% 23.02/3.51  --abstr_ref_until_sat                   false
% 23.02/3.51  --abstr_ref_sig_restrict                funpre
% 23.02/3.51  --abstr_ref_af_restrict_to_split_sk     false
% 23.02/3.51  --abstr_ref_under                       []
% 23.02/3.51  
% 23.02/3.51  ------ SAT Options
% 23.02/3.51  
% 23.02/3.51  --sat_mode                              false
% 23.02/3.51  --sat_fm_restart_options                ""
% 23.02/3.51  --sat_gr_def                            false
% 23.02/3.51  --sat_epr_types                         true
% 23.02/3.51  --sat_non_cyclic_types                  false
% 23.02/3.51  --sat_finite_models                     false
% 23.02/3.51  --sat_fm_lemmas                         false
% 23.02/3.51  --sat_fm_prep                           false
% 23.02/3.51  --sat_fm_uc_incr                        true
% 23.02/3.51  --sat_out_model                         small
% 23.02/3.51  --sat_out_clauses                       false
% 23.02/3.51  
% 23.02/3.51  ------ QBF Options
% 23.02/3.51  
% 23.02/3.51  --qbf_mode                              false
% 23.02/3.51  --qbf_elim_univ                         false
% 23.02/3.51  --qbf_dom_inst                          none
% 23.02/3.51  --qbf_dom_pre_inst                      false
% 23.02/3.51  --qbf_sk_in                             false
% 23.02/3.51  --qbf_pred_elim                         true
% 23.02/3.51  --qbf_split                             512
% 23.02/3.51  
% 23.02/3.51  ------ BMC1 Options
% 23.02/3.51  
% 23.02/3.51  --bmc1_incremental                      false
% 23.02/3.51  --bmc1_axioms                           reachable_all
% 23.02/3.51  --bmc1_min_bound                        0
% 23.02/3.51  --bmc1_max_bound                        -1
% 23.02/3.51  --bmc1_max_bound_default                -1
% 23.02/3.51  --bmc1_symbol_reachability              true
% 23.02/3.51  --bmc1_property_lemmas                  false
% 23.02/3.51  --bmc1_k_induction                      false
% 23.02/3.51  --bmc1_non_equiv_states                 false
% 23.02/3.51  --bmc1_deadlock                         false
% 23.02/3.51  --bmc1_ucm                              false
% 23.02/3.51  --bmc1_add_unsat_core                   none
% 23.02/3.51  --bmc1_unsat_core_children              false
% 23.02/3.51  --bmc1_unsat_core_extrapolate_axioms    false
% 23.02/3.51  --bmc1_out_stat                         full
% 23.02/3.51  --bmc1_ground_init                      false
% 23.02/3.51  --bmc1_pre_inst_next_state              false
% 23.02/3.51  --bmc1_pre_inst_state                   false
% 23.02/3.51  --bmc1_pre_inst_reach_state             false
% 23.02/3.51  --bmc1_out_unsat_core                   false
% 23.02/3.51  --bmc1_aig_witness_out                  false
% 23.02/3.51  --bmc1_verbose                          false
% 23.02/3.51  --bmc1_dump_clauses_tptp                false
% 23.02/3.51  --bmc1_dump_unsat_core_tptp             false
% 23.02/3.51  --bmc1_dump_file                        -
% 23.02/3.51  --bmc1_ucm_expand_uc_limit              128
% 23.02/3.51  --bmc1_ucm_n_expand_iterations          6
% 23.02/3.51  --bmc1_ucm_extend_mode                  1
% 23.02/3.51  --bmc1_ucm_init_mode                    2
% 23.02/3.51  --bmc1_ucm_cone_mode                    none
% 23.02/3.51  --bmc1_ucm_reduced_relation_type        0
% 23.02/3.51  --bmc1_ucm_relax_model                  4
% 23.02/3.51  --bmc1_ucm_full_tr_after_sat            true
% 23.02/3.51  --bmc1_ucm_expand_neg_assumptions       false
% 23.02/3.51  --bmc1_ucm_layered_model                none
% 23.02/3.51  --bmc1_ucm_max_lemma_size               10
% 23.02/3.51  
% 23.02/3.51  ------ AIG Options
% 23.02/3.51  
% 23.02/3.51  --aig_mode                              false
% 23.02/3.51  
% 23.02/3.51  ------ Instantiation Options
% 23.02/3.51  
% 23.02/3.51  --instantiation_flag                    true
% 23.02/3.51  --inst_sos_flag                         false
% 23.02/3.51  --inst_sos_phase                        true
% 23.02/3.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.02/3.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.02/3.51  --inst_lit_sel_side                     none
% 23.02/3.51  --inst_solver_per_active                1400
% 23.02/3.51  --inst_solver_calls_frac                1.
% 23.02/3.51  --inst_passive_queue_type               priority_queues
% 23.02/3.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.02/3.51  --inst_passive_queues_freq              [25;2]
% 23.02/3.51  --inst_dismatching                      true
% 23.02/3.51  --inst_eager_unprocessed_to_passive     true
% 23.02/3.51  --inst_prop_sim_given                   true
% 23.02/3.51  --inst_prop_sim_new                     false
% 23.02/3.51  --inst_subs_new                         false
% 23.02/3.51  --inst_eq_res_simp                      false
% 23.02/3.51  --inst_subs_given                       false
% 23.02/3.51  --inst_orphan_elimination               true
% 23.02/3.51  --inst_learning_loop_flag               true
% 23.02/3.51  --inst_learning_start                   3000
% 23.02/3.51  --inst_learning_factor                  2
% 23.02/3.51  --inst_start_prop_sim_after_learn       3
% 23.02/3.51  --inst_sel_renew                        solver
% 23.02/3.51  --inst_lit_activity_flag                true
% 23.02/3.51  --inst_restr_to_given                   false
% 23.02/3.51  --inst_activity_threshold               500
% 23.02/3.51  --inst_out_proof                        true
% 23.02/3.51  
% 23.02/3.51  ------ Resolution Options
% 23.02/3.51  
% 23.02/3.51  --resolution_flag                       false
% 23.02/3.51  --res_lit_sel                           adaptive
% 23.02/3.51  --res_lit_sel_side                      none
% 23.02/3.51  --res_ordering                          kbo
% 23.02/3.51  --res_to_prop_solver                    active
% 23.02/3.51  --res_prop_simpl_new                    false
% 23.02/3.51  --res_prop_simpl_given                  true
% 23.02/3.51  --res_passive_queue_type                priority_queues
% 23.02/3.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.02/3.51  --res_passive_queues_freq               [15;5]
% 23.02/3.51  --res_forward_subs                      full
% 23.02/3.51  --res_backward_subs                     full
% 23.02/3.51  --res_forward_subs_resolution           true
% 23.02/3.51  --res_backward_subs_resolution          true
% 23.02/3.51  --res_orphan_elimination                true
% 23.02/3.51  --res_time_limit                        2.
% 23.02/3.51  --res_out_proof                         true
% 23.02/3.51  
% 23.02/3.51  ------ Superposition Options
% 23.02/3.51  
% 23.02/3.51  --superposition_flag                    true
% 23.02/3.51  --sup_passive_queue_type                priority_queues
% 23.02/3.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.02/3.51  --sup_passive_queues_freq               [8;1;4]
% 23.02/3.51  --demod_completeness_check              fast
% 23.02/3.51  --demod_use_ground                      true
% 23.02/3.51  --sup_to_prop_solver                    passive
% 23.02/3.51  --sup_prop_simpl_new                    true
% 23.02/3.51  --sup_prop_simpl_given                  true
% 23.02/3.51  --sup_fun_splitting                     false
% 23.02/3.51  --sup_smt_interval                      50000
% 23.02/3.51  
% 23.02/3.51  ------ Superposition Simplification Setup
% 23.02/3.51  
% 23.02/3.51  --sup_indices_passive                   []
% 23.02/3.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.02/3.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.02/3.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.02/3.51  --sup_full_triv                         [TrivRules;PropSubs]
% 23.02/3.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.02/3.51  --sup_full_bw                           [BwDemod]
% 23.02/3.51  --sup_immed_triv                        [TrivRules]
% 23.02/3.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.02/3.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.02/3.51  --sup_immed_bw_main                     []
% 23.02/3.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.02/3.51  --sup_input_triv                        [Unflattening;TrivRules]
% 23.02/3.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.02/3.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.02/3.51  
% 23.02/3.51  ------ Combination Options
% 23.02/3.51  
% 23.02/3.51  --comb_res_mult                         3
% 23.02/3.51  --comb_sup_mult                         2
% 23.02/3.51  --comb_inst_mult                        10
% 23.02/3.51  
% 23.02/3.51  ------ Debug Options
% 23.02/3.51  
% 23.02/3.51  --dbg_backtrace                         false
% 23.02/3.51  --dbg_dump_prop_clauses                 false
% 23.02/3.51  --dbg_dump_prop_clauses_file            -
% 23.02/3.51  --dbg_out_stat                          false
% 23.02/3.51  
% 23.02/3.51  
% 23.02/3.51  
% 23.02/3.51  
% 23.02/3.51  ------ Proving...
% 23.02/3.51  
% 23.02/3.51  
% 23.02/3.51  % SZS status Theorem for theBenchmark.p
% 23.02/3.51  
% 23.02/3.51  % SZS output start CNFRefutation for theBenchmark.p
% 23.02/3.51  
% 23.02/3.51  fof(f41,plain,(
% 23.02/3.51    ! [X1,X3,X4,X0,X2] : (sP0(X1,X3,X4,X0,X2) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))),
% 23.02/3.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 23.02/3.51  
% 23.02/3.51  fof(f51,plain,(
% 23.02/3.51    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 23.02/3.51    inference(nnf_transformation,[],[f41])).
% 23.02/3.51  
% 23.02/3.51  fof(f52,plain,(
% 23.02/3.51    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 23.02/3.51    inference(flattening,[],[f51])).
% 23.02/3.51  
% 23.02/3.51  fof(f53,plain,(
% 23.02/3.51    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) & ((m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 23.02/3.51    inference(rectify,[],[f52])).
% 23.02/3.51  
% 23.02/3.51  fof(f90,plain,(
% 23.02/3.51    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 23.02/3.51    inference(cnf_transformation,[],[f53])).
% 23.02/3.51  
% 23.02/3.51  fof(f93,plain,(
% 23.02/3.51    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 23.02/3.51    inference(cnf_transformation,[],[f53])).
% 23.02/3.51  
% 23.02/3.51  fof(f94,plain,(
% 23.02/3.51    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 23.02/3.51    inference(cnf_transformation,[],[f53])).
% 23.02/3.51  
% 23.02/3.51  fof(f16,conjecture,(
% 23.02/3.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 23.02/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.02/3.51  
% 23.02/3.51  fof(f17,negated_conjecture,(
% 23.02/3.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 23.02/3.51    inference(negated_conjecture,[],[f16])).
% 23.02/3.51  
% 23.02/3.51  fof(f39,plain,(
% 23.02/3.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & (r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0)) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 23.02/3.51    inference(ennf_transformation,[],[f17])).
% 23.02/3.51  
% 23.02/3.51  fof(f40,plain,(
% 23.02/3.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 23.02/3.51    inference(flattening,[],[f39])).
% 23.02/3.51  
% 23.02/3.51  fof(f54,plain,(
% 23.02/3.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 23.02/3.51    inference(nnf_transformation,[],[f40])).
% 23.02/3.51  
% 23.02/3.51  fof(f55,plain,(
% 23.02/3.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 23.02/3.51    inference(flattening,[],[f54])).
% 23.02/3.51  
% 23.02/3.51  fof(f60,plain,(
% 23.02/3.51    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((~m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,sK6) & k1_tsep_1(X0,X3,sK6) = X0 & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 23.02/3.51    introduced(choice_axiom,[])).
% 23.02/3.51  
% 23.02/3.51  fof(f59,plain,(
% 23.02/3.51    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK5)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK5))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,sK5,X4) & k1_tsep_1(X0,sK5,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 23.02/3.51    introduced(choice_axiom,[])).
% 23.02/3.51  
% 23.02/3.51  fof(f58,plain,(
% 23.02/3.51    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(sK4,X0,X1) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) & m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X3))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK4,X0,X1) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 23.02/3.51    introduced(choice_axiom,[])).
% 23.02/3.51  
% 23.02/3.51  fof(f57,plain,(
% 23.02/3.51    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(X2,X0,sK3) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) & m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v5_pre_topc(X2,X0,sK3) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 23.02/3.51    introduced(choice_axiom,[])).
% 23.02/3.51  
% 23.02/3.51  fof(f56,plain,(
% 23.02/3.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(sK2,X3,X4) & k1_tsep_1(sK2,X3,X4) = sK2 & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 23.02/3.51    introduced(choice_axiom,[])).
% 23.02/3.51  
% 23.02/3.51  fof(f61,plain,(
% 23.02/3.51    (((((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,sK5,sK6) & k1_tsep_1(sK2,sK5,sK6) = sK2 & m1_pre_topc(sK6,sK2) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 23.02/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f55,f60,f59,f58,f57,f56])).
% 23.02/3.51  
% 23.02/3.51  fof(f111,plain,(
% 23.02/3.51    k1_tsep_1(sK2,sK5,sK6) = sK2),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  fof(f13,axiom,(
% 23.02/3.51    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 23.02/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.02/3.51  
% 23.02/3.51  fof(f18,plain,(
% 23.02/3.51    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 23.02/3.51    inference(pure_predicate_removal,[],[f13])).
% 23.02/3.51  
% 23.02/3.51  fof(f33,plain,(
% 23.02/3.51    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 23.02/3.51    inference(ennf_transformation,[],[f18])).
% 23.02/3.51  
% 23.02/3.51  fof(f34,plain,(
% 23.02/3.51    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 23.02/3.51    inference(flattening,[],[f33])).
% 23.02/3.51  
% 23.02/3.51  fof(f79,plain,(
% 23.02/3.51    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.02/3.51    inference(cnf_transformation,[],[f34])).
% 23.02/3.51  
% 23.02/3.51  fof(f98,plain,(
% 23.02/3.51    ~v2_struct_0(sK2)),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  fof(f100,plain,(
% 23.02/3.51    l1_pre_topc(sK2)),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  fof(f107,plain,(
% 23.02/3.51    ~v2_struct_0(sK5)),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  fof(f108,plain,(
% 23.02/3.51    m1_pre_topc(sK5,sK2)),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  fof(f109,plain,(
% 23.02/3.51    ~v2_struct_0(sK6)),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  fof(f110,plain,(
% 23.02/3.51    m1_pre_topc(sK6,sK2)),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  fof(f106,plain,(
% 23.02/3.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  fof(f12,axiom,(
% 23.02/3.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 23.02/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.02/3.51  
% 23.02/3.51  fof(f31,plain,(
% 23.02/3.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.02/3.51    inference(ennf_transformation,[],[f12])).
% 23.02/3.51  
% 23.02/3.51  fof(f32,plain,(
% 23.02/3.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.02/3.51    inference(flattening,[],[f31])).
% 23.02/3.51  
% 23.02/3.51  fof(f77,plain,(
% 23.02/3.51    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.02/3.51    inference(cnf_transformation,[],[f32])).
% 23.02/3.51  
% 23.02/3.51  fof(f9,axiom,(
% 23.02/3.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 23.02/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.02/3.51  
% 23.02/3.51  fof(f27,plain,(
% 23.02/3.51    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 23.02/3.51    inference(ennf_transformation,[],[f9])).
% 23.02/3.51  
% 23.02/3.51  fof(f28,plain,(
% 23.02/3.51    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 23.02/3.51    inference(flattening,[],[f27])).
% 23.02/3.51  
% 23.02/3.51  fof(f74,plain,(
% 23.02/3.51    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 23.02/3.51    inference(cnf_transformation,[],[f28])).
% 23.02/3.51  
% 23.02/3.51  fof(f104,plain,(
% 23.02/3.51    v1_funct_1(sK4)),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  fof(f99,plain,(
% 23.02/3.51    v2_pre_topc(sK2)),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  fof(f101,plain,(
% 23.02/3.51    ~v2_struct_0(sK3)),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  fof(f102,plain,(
% 23.02/3.51    v2_pre_topc(sK3)),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  fof(f103,plain,(
% 23.02/3.51    l1_pre_topc(sK3)),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  fof(f105,plain,(
% 23.02/3.51    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  fof(f8,axiom,(
% 23.02/3.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 23.02/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.02/3.51  
% 23.02/3.51  fof(f19,plain,(
% 23.02/3.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 23.02/3.51    inference(pure_predicate_removal,[],[f8])).
% 23.02/3.51  
% 23.02/3.51  fof(f26,plain,(
% 23.02/3.51    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.02/3.51    inference(ennf_transformation,[],[f19])).
% 23.02/3.51  
% 23.02/3.51  fof(f73,plain,(
% 23.02/3.51    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.02/3.51    inference(cnf_transformation,[],[f26])).
% 23.02/3.51  
% 23.02/3.51  fof(f5,axiom,(
% 23.02/3.51    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 23.02/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.02/3.51  
% 23.02/3.51  fof(f23,plain,(
% 23.02/3.51    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 23.02/3.51    inference(ennf_transformation,[],[f5])).
% 23.02/3.51  
% 23.02/3.51  fof(f47,plain,(
% 23.02/3.51    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 23.02/3.51    inference(nnf_transformation,[],[f23])).
% 23.02/3.51  
% 23.02/3.51  fof(f69,plain,(
% 23.02/3.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 23.02/3.51    inference(cnf_transformation,[],[f47])).
% 23.02/3.51  
% 23.02/3.51  fof(f3,axiom,(
% 23.02/3.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 23.02/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.02/3.51  
% 23.02/3.51  fof(f46,plain,(
% 23.02/3.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 23.02/3.51    inference(nnf_transformation,[],[f3])).
% 23.02/3.51  
% 23.02/3.51  fof(f66,plain,(
% 23.02/3.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 23.02/3.51    inference(cnf_transformation,[],[f46])).
% 23.02/3.51  
% 23.02/3.51  fof(f4,axiom,(
% 23.02/3.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 23.02/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.02/3.51  
% 23.02/3.51  fof(f22,plain,(
% 23.02/3.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 23.02/3.51    inference(ennf_transformation,[],[f4])).
% 23.02/3.51  
% 23.02/3.51  fof(f68,plain,(
% 23.02/3.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 23.02/3.51    inference(cnf_transformation,[],[f22])).
% 23.02/3.51  
% 23.02/3.51  fof(f67,plain,(
% 23.02/3.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 23.02/3.51    inference(cnf_transformation,[],[f46])).
% 23.02/3.51  
% 23.02/3.51  fof(f6,axiom,(
% 23.02/3.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 23.02/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.02/3.51  
% 23.02/3.51  fof(f71,plain,(
% 23.02/3.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 23.02/3.51    inference(cnf_transformation,[],[f6])).
% 23.02/3.51  
% 23.02/3.51  fof(f7,axiom,(
% 23.02/3.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 23.02/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.02/3.51  
% 23.02/3.51  fof(f24,plain,(
% 23.02/3.51    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 23.02/3.51    inference(ennf_transformation,[],[f7])).
% 23.02/3.51  
% 23.02/3.51  fof(f25,plain,(
% 23.02/3.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 23.02/3.51    inference(flattening,[],[f24])).
% 23.02/3.51  
% 23.02/3.51  fof(f72,plain,(
% 23.02/3.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 23.02/3.51    inference(cnf_transformation,[],[f25])).
% 23.02/3.51  
% 23.02/3.51  fof(f42,plain,(
% 23.02/3.51    ! [X2,X0,X4,X3,X1] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> sP0(X1,X3,X4,X0,X2)) | ~sP1(X2,X0,X4,X3,X1))),
% 23.02/3.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 23.02/3.51  
% 23.02/3.51  fof(f48,plain,(
% 23.02/3.51    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))))) | ~sP1(X2,X0,X4,X3,X1))),
% 23.02/3.51    inference(nnf_transformation,[],[f42])).
% 23.02/3.51  
% 23.02/3.51  fof(f49,plain,(
% 23.02/3.51    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))))) | ~sP1(X2,X0,X4,X3,X1))),
% 23.02/3.51    inference(flattening,[],[f48])).
% 23.02/3.51  
% 23.02/3.51  fof(f50,plain,(
% 23.02/3.51    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) & v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) & v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) & v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))))) | ~sP1(X0,X1,X2,X3,X4))),
% 23.02/3.51    inference(rectify,[],[f49])).
% 23.02/3.51  
% 23.02/3.51  fof(f83,plain,(
% 23.02/3.51    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) | ~sP1(X0,X1,X2,X3,X4)) )),
% 23.02/3.51    inference(cnf_transformation,[],[f50])).
% 23.02/3.51  
% 23.02/3.51  fof(f15,axiom,(
% 23.02/3.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))))))))),
% 23.02/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.02/3.51  
% 23.02/3.51  fof(f37,plain,(
% 23.02/3.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.02/3.51    inference(ennf_transformation,[],[f15])).
% 23.02/3.51  
% 23.02/3.51  fof(f38,plain,(
% 23.02/3.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.02/3.51    inference(flattening,[],[f37])).
% 23.02/3.51  
% 23.02/3.51  fof(f43,plain,(
% 23.02/3.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X2,X0,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.02/3.51    inference(definition_folding,[],[f38,f42,f41])).
% 23.02/3.51  
% 23.02/3.51  fof(f97,plain,(
% 23.02/3.51    ( ! [X4,X2,X0,X3,X1] : (sP1(X2,X0,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.02/3.51    inference(cnf_transformation,[],[f43])).
% 23.02/3.51  
% 23.02/3.51  fof(f112,plain,(
% 23.02/3.51    r4_tsep_1(sK2,sK5,sK6)),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  fof(f87,plain,(
% 23.02/3.51    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 23.02/3.51    inference(cnf_transformation,[],[f50])).
% 23.02/3.51  
% 23.02/3.51  fof(f143,plain,(
% 23.02/3.51    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  fof(f96,plain,(
% 23.02/3.51    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) )),
% 23.02/3.51    inference(cnf_transformation,[],[f53])).
% 23.02/3.51  
% 23.02/3.51  fof(f135,plain,(
% 23.02/3.51    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  fof(f139,plain,(
% 23.02/3.51    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  fof(f10,axiom,(
% 23.02/3.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 23.02/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.02/3.51  
% 23.02/3.51  fof(f29,plain,(
% 23.02/3.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 23.02/3.51    inference(ennf_transformation,[],[f10])).
% 23.02/3.51  
% 23.02/3.51  fof(f75,plain,(
% 23.02/3.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 23.02/3.51    inference(cnf_transformation,[],[f29])).
% 23.02/3.51  
% 23.02/3.51  fof(f11,axiom,(
% 23.02/3.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 23.02/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.02/3.51  
% 23.02/3.51  fof(f30,plain,(
% 23.02/3.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.02/3.51    inference(ennf_transformation,[],[f11])).
% 23.02/3.51  
% 23.02/3.51  fof(f76,plain,(
% 23.02/3.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.02/3.51    inference(cnf_transformation,[],[f30])).
% 23.02/3.51  
% 23.02/3.51  fof(f14,axiom,(
% 23.02/3.51    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 23.02/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.02/3.51  
% 23.02/3.51  fof(f35,plain,(
% 23.02/3.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 23.02/3.51    inference(ennf_transformation,[],[f14])).
% 23.02/3.51  
% 23.02/3.51  fof(f36,plain,(
% 23.02/3.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 23.02/3.51    inference(flattening,[],[f35])).
% 23.02/3.51  
% 23.02/3.51  fof(f80,plain,(
% 23.02/3.51    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 23.02/3.51    inference(cnf_transformation,[],[f36])).
% 23.02/3.51  
% 23.02/3.51  fof(f86,plain,(
% 23.02/3.51    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 23.02/3.51    inference(cnf_transformation,[],[f50])).
% 23.02/3.51  
% 23.02/3.51  fof(f81,plain,(
% 23.02/3.51    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 23.02/3.51    inference(cnf_transformation,[],[f36])).
% 23.02/3.51  
% 23.02/3.51  fof(f127,plain,(
% 23.02/3.51    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  fof(f119,plain,(
% 23.02/3.51    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  fof(f123,plain,(
% 23.02/3.51    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  fof(f84,plain,(
% 23.02/3.51    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 23.02/3.51    inference(cnf_transformation,[],[f50])).
% 23.02/3.51  
% 23.02/3.51  fof(f82,plain,(
% 23.02/3.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 23.02/3.51    inference(cnf_transformation,[],[f36])).
% 23.02/3.51  
% 23.02/3.51  fof(f145,plain,(
% 23.02/3.51    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 23.02/3.51    inference(cnf_transformation,[],[f61])).
% 23.02/3.51  
% 23.02/3.51  cnf(c_32,plain,
% 23.02/3.51      ( ~ sP0(X0,X1,X2,X3,X4)
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) ),
% 23.02/3.51      inference(cnf_transformation,[],[f90]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_74463,plain,
% 23.02/3.51      ( ~ sP0(X0,sK6,sK4,sK2,sK5)
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,X0,sK4,sK5),sK5,X0) ),
% 23.02/3.51      inference(instantiation,[status(thm)],[c_32]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_74495,plain,
% 23.02/3.51      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
% 23.02/3.51      inference(instantiation,[status(thm)],[c_74463]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_29,plain,
% 23.02/3.51      ( ~ sP0(X0,X1,X2,X3,X4)
% 23.02/3.51      | v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) ),
% 23.02/3.51      inference(cnf_transformation,[],[f93]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_74465,plain,
% 23.02/3.51      ( ~ sP0(X0,sK6,sK4,sK2,sK5)
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,X0,sK4,sK6),u1_struct_0(sK6),u1_struct_0(X0)) ),
% 23.02/3.51      inference(instantiation,[status(thm)],[c_29]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_74487,plain,
% 23.02/3.51      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
% 23.02/3.51      inference(instantiation,[status(thm)],[c_74465]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_28,plain,
% 23.02/3.51      ( ~ sP0(X0,X1,X2,X3,X4)
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) ),
% 23.02/3.51      inference(cnf_transformation,[],[f94]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_74466,plain,
% 23.02/3.51      ( ~ sP0(X0,sK6,sK4,sK2,sK5)
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,X0,sK4,sK6),sK6,X0) ),
% 23.02/3.51      inference(instantiation,[status(thm)],[c_28]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_74483,plain,
% 23.02/3.51      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
% 23.02/3.51      inference(instantiation,[status(thm)],[c_74466]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_70,negated_conjecture,
% 23.02/3.51      ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
% 23.02/3.51      inference(cnf_transformation,[],[f111]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_16,plain,
% 23.02/3.51      ( ~ m1_pre_topc(X0,X1)
% 23.02/3.51      | ~ m1_pre_topc(X2,X1)
% 23.02/3.51      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 23.02/3.51      | v2_struct_0(X1)
% 23.02/3.51      | v2_struct_0(X0)
% 23.02/3.51      | v2_struct_0(X2)
% 23.02/3.51      | ~ l1_pre_topc(X1) ),
% 23.02/3.51      inference(cnf_transformation,[],[f79]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4048,plain,
% 23.02/3.51      ( m1_pre_topc(X0,X1) != iProver_top
% 23.02/3.51      | m1_pre_topc(X2,X1) != iProver_top
% 23.02/3.51      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1) = iProver_top
% 23.02/3.51      | v2_struct_0(X1) = iProver_top
% 23.02/3.51      | v2_struct_0(X0) = iProver_top
% 23.02/3.51      | v2_struct_0(X2) = iProver_top
% 23.02/3.51      | l1_pre_topc(X1) != iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_10071,plain,
% 23.02/3.51      ( m1_pre_topc(sK5,sK2) != iProver_top
% 23.02/3.51      | m1_pre_topc(sK6,sK2) != iProver_top
% 23.02/3.51      | m1_pre_topc(sK2,sK2) = iProver_top
% 23.02/3.51      | v2_struct_0(sK5) = iProver_top
% 23.02/3.51      | v2_struct_0(sK6) = iProver_top
% 23.02/3.51      | v2_struct_0(sK2) = iProver_top
% 23.02/3.51      | l1_pre_topc(sK2) != iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_70,c_4048]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_83,negated_conjecture,
% 23.02/3.51      ( ~ v2_struct_0(sK2) ),
% 23.02/3.51      inference(cnf_transformation,[],[f98]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_84,plain,
% 23.02/3.51      ( v2_struct_0(sK2) != iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_83]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_81,negated_conjecture,
% 23.02/3.51      ( l1_pre_topc(sK2) ),
% 23.02/3.51      inference(cnf_transformation,[],[f100]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_86,plain,
% 23.02/3.51      ( l1_pre_topc(sK2) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_81]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_74,negated_conjecture,
% 23.02/3.51      ( ~ v2_struct_0(sK5) ),
% 23.02/3.51      inference(cnf_transformation,[],[f107]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_93,plain,
% 23.02/3.51      ( v2_struct_0(sK5) != iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_74]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_73,negated_conjecture,
% 23.02/3.51      ( m1_pre_topc(sK5,sK2) ),
% 23.02/3.51      inference(cnf_transformation,[],[f108]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_94,plain,
% 23.02/3.51      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_73]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_72,negated_conjecture,
% 23.02/3.51      ( ~ v2_struct_0(sK6) ),
% 23.02/3.51      inference(cnf_transformation,[],[f109]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_95,plain,
% 23.02/3.51      ( v2_struct_0(sK6) != iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_72]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_71,negated_conjecture,
% 23.02/3.51      ( m1_pre_topc(sK6,sK2) ),
% 23.02/3.51      inference(cnf_transformation,[],[f110]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_96,plain,
% 23.02/3.51      ( m1_pre_topc(sK6,sK2) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_71]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_10219,plain,
% 23.02/3.51      ( m1_pre_topc(sK2,sK2) = iProver_top ),
% 23.02/3.51      inference(global_propositional_subsumption,
% 23.02/3.51                [status(thm)],
% 23.02/3.51                [c_10071,c_84,c_86,c_93,c_94,c_95,c_96]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_75,negated_conjecture,
% 23.02/3.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 23.02/3.51      inference(cnf_transformation,[],[f106]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4022,plain,
% 23.02/3.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_75]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_15,plain,
% 23.02/3.51      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.02/3.51      | ~ m1_pre_topc(X3,X1)
% 23.02/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.02/3.51      | v2_struct_0(X1)
% 23.02/3.51      | v2_struct_0(X2)
% 23.02/3.51      | ~ v2_pre_topc(X2)
% 23.02/3.51      | ~ v2_pre_topc(X1)
% 23.02/3.51      | ~ l1_pre_topc(X1)
% 23.02/3.51      | ~ l1_pre_topc(X2)
% 23.02/3.51      | ~ v1_funct_1(X0)
% 23.02/3.51      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 23.02/3.51      inference(cnf_transformation,[],[f77]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4049,plain,
% 23.02/3.51      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
% 23.02/3.51      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 23.02/3.51      | m1_pre_topc(X3,X0) != iProver_top
% 23.02/3.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 23.02/3.51      | v2_struct_0(X0) = iProver_top
% 23.02/3.51      | v2_struct_0(X1) = iProver_top
% 23.02/3.51      | v2_pre_topc(X0) != iProver_top
% 23.02/3.51      | v2_pre_topc(X1) != iProver_top
% 23.02/3.51      | l1_pre_topc(X0) != iProver_top
% 23.02/3.51      | l1_pre_topc(X1) != iProver_top
% 23.02/3.51      | v1_funct_1(X2) != iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_11460,plain,
% 23.02/3.51      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0)) = k2_tmap_1(sK2,sK3,sK4,X0)
% 23.02/3.51      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | m1_pre_topc(X0,sK2) != iProver_top
% 23.02/3.51      | v2_struct_0(sK3) = iProver_top
% 23.02/3.51      | v2_struct_0(sK2) = iProver_top
% 23.02/3.51      | v2_pre_topc(sK3) != iProver_top
% 23.02/3.51      | v2_pre_topc(sK2) != iProver_top
% 23.02/3.51      | l1_pre_topc(sK3) != iProver_top
% 23.02/3.51      | l1_pre_topc(sK2) != iProver_top
% 23.02/3.51      | v1_funct_1(sK4) != iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_4022,c_4049]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_12,plain,
% 23.02/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.02/3.51      | ~ v1_funct_1(X0)
% 23.02/3.51      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 23.02/3.51      inference(cnf_transformation,[],[f74]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4052,plain,
% 23.02/3.51      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 23.02/3.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 23.02/3.51      | v1_funct_1(X2) != iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_9271,plain,
% 23.02/3.51      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k7_relat_1(sK4,X0)
% 23.02/3.51      | v1_funct_1(sK4) != iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_4022,c_4052]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_77,negated_conjecture,
% 23.02/3.51      ( v1_funct_1(sK4) ),
% 23.02/3.51      inference(cnf_transformation,[],[f104]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4635,plain,
% 23.02/3.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.02/3.51      | ~ v1_funct_1(sK4)
% 23.02/3.51      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 23.02/3.51      inference(instantiation,[status(thm)],[c_12]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4796,plain,
% 23.02/3.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 23.02/3.51      | ~ v1_funct_1(sK4)
% 23.02/3.51      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k7_relat_1(sK4,X0) ),
% 23.02/3.51      inference(instantiation,[status(thm)],[c_4635]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_9408,plain,
% 23.02/3.51      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k7_relat_1(sK4,X0) ),
% 23.02/3.51      inference(global_propositional_subsumption,
% 23.02/3.51                [status(thm)],
% 23.02/3.51                [c_9271,c_77,c_75,c_4796]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_11500,plain,
% 23.02/3.51      ( k2_tmap_1(sK2,sK3,sK4,X0) = k7_relat_1(sK4,u1_struct_0(X0))
% 23.02/3.51      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | m1_pre_topc(X0,sK2) != iProver_top
% 23.02/3.51      | v2_struct_0(sK3) = iProver_top
% 23.02/3.51      | v2_struct_0(sK2) = iProver_top
% 23.02/3.51      | v2_pre_topc(sK3) != iProver_top
% 23.02/3.51      | v2_pre_topc(sK2) != iProver_top
% 23.02/3.51      | l1_pre_topc(sK3) != iProver_top
% 23.02/3.51      | l1_pre_topc(sK2) != iProver_top
% 23.02/3.51      | v1_funct_1(sK4) != iProver_top ),
% 23.02/3.51      inference(demodulation,[status(thm)],[c_11460,c_9408]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_82,negated_conjecture,
% 23.02/3.51      ( v2_pre_topc(sK2) ),
% 23.02/3.51      inference(cnf_transformation,[],[f99]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_85,plain,
% 23.02/3.51      ( v2_pre_topc(sK2) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_82]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_80,negated_conjecture,
% 23.02/3.51      ( ~ v2_struct_0(sK3) ),
% 23.02/3.51      inference(cnf_transformation,[],[f101]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_87,plain,
% 23.02/3.51      ( v2_struct_0(sK3) != iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_80]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_79,negated_conjecture,
% 23.02/3.51      ( v2_pre_topc(sK3) ),
% 23.02/3.51      inference(cnf_transformation,[],[f102]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_88,plain,
% 23.02/3.51      ( v2_pre_topc(sK3) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_79]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_78,negated_conjecture,
% 23.02/3.51      ( l1_pre_topc(sK3) ),
% 23.02/3.51      inference(cnf_transformation,[],[f103]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_89,plain,
% 23.02/3.51      ( l1_pre_topc(sK3) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_78]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_90,plain,
% 23.02/3.51      ( v1_funct_1(sK4) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_77]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_76,negated_conjecture,
% 23.02/3.51      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 23.02/3.51      inference(cnf_transformation,[],[f105]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_91,plain,
% 23.02/3.51      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_76]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_26259,plain,
% 23.02/3.51      ( m1_pre_topc(X0,sK2) != iProver_top
% 23.02/3.51      | k2_tmap_1(sK2,sK3,sK4,X0) = k7_relat_1(sK4,u1_struct_0(X0)) ),
% 23.02/3.51      inference(global_propositional_subsumption,
% 23.02/3.51                [status(thm)],
% 23.02/3.51                [c_11500,c_84,c_85,c_86,c_87,c_88,c_89,c_90,c_91]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_26260,plain,
% 23.02/3.51      ( k2_tmap_1(sK2,sK3,sK4,X0) = k7_relat_1(sK4,u1_struct_0(X0))
% 23.02/3.51      | m1_pre_topc(X0,sK2) != iProver_top ),
% 23.02/3.51      inference(renaming,[status(thm)],[c_26259]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_26270,plain,
% 23.02/3.51      ( k2_tmap_1(sK2,sK3,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_10219,c_26260]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_11,plain,
% 23.02/3.51      ( v4_relat_1(X0,X1)
% 23.02/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 23.02/3.51      inference(cnf_transformation,[],[f73]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_8,plain,
% 23.02/3.51      ( ~ v4_relat_1(X0,X1)
% 23.02/3.51      | r1_tarski(k1_relat_1(X0),X1)
% 23.02/3.51      | ~ v1_relat_1(X0) ),
% 23.02/3.51      inference(cnf_transformation,[],[f69]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_967,plain,
% 23.02/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.02/3.51      | r1_tarski(k1_relat_1(X0),X1)
% 23.02/3.51      | ~ v1_relat_1(X0) ),
% 23.02/3.51      inference(resolution,[status(thm)],[c_11,c_8]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4011,plain,
% 23.02/3.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.02/3.51      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 23.02/3.51      | v1_relat_1(X0) != iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_967]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4742,plain,
% 23.02/3.51      ( r1_tarski(k1_relat_1(sK4),u1_struct_0(sK2)) = iProver_top
% 23.02/3.51      | v1_relat_1(sK4) != iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_4022,c_4011]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_5,plain,
% 23.02/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 23.02/3.51      inference(cnf_transformation,[],[f66]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4055,plain,
% 23.02/3.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.02/3.51      | r1_tarski(X0,X1) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_5270,plain,
% 23.02/3.51      ( r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) = iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_4022,c_4055]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_6,plain,
% 23.02/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.02/3.51      | ~ v1_relat_1(X1)
% 23.02/3.51      | v1_relat_1(X0) ),
% 23.02/3.51      inference(cnf_transformation,[],[f68]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4,plain,
% 23.02/3.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 23.02/3.51      inference(cnf_transformation,[],[f67]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_652,plain,
% 23.02/3.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 23.02/3.51      inference(prop_impl,[status(thm)],[c_4]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_653,plain,
% 23.02/3.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 23.02/3.51      inference(renaming,[status(thm)],[c_652]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_772,plain,
% 23.02/3.51      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 23.02/3.51      inference(bin_hyper_res,[status(thm)],[c_6,c_653]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4703,plain,
% 23.02/3.51      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 23.02/3.51      | v1_relat_1(X0)
% 23.02/3.51      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 23.02/3.51      inference(instantiation,[status(thm)],[c_772]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_5593,plain,
% 23.02/3.51      ( ~ r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
% 23.02/3.51      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
% 23.02/3.51      | v1_relat_1(sK4) ),
% 23.02/3.51      inference(instantiation,[status(thm)],[c_4703]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_5594,plain,
% 23.02/3.51      ( r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != iProver_top
% 23.02/3.51      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != iProver_top
% 23.02/3.51      | v1_relat_1(sK4) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_5593]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_9,plain,
% 23.02/3.51      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 23.02/3.51      inference(cnf_transformation,[],[f71]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_6786,plain,
% 23.02/3.51      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
% 23.02/3.51      inference(instantiation,[status(thm)],[c_9]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_6787,plain,
% 23.02/3.51      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_6786]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_7038,plain,
% 23.02/3.51      ( r1_tarski(k1_relat_1(sK4),u1_struct_0(sK2)) = iProver_top ),
% 23.02/3.51      inference(global_propositional_subsumption,
% 23.02/3.51                [status(thm)],
% 23.02/3.51                [c_4742,c_5270,c_5594,c_6787]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_10,plain,
% 23.02/3.51      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 23.02/3.51      | ~ v1_relat_1(X0)
% 23.02/3.51      | k7_relat_1(X0,X1) = X0 ),
% 23.02/3.51      inference(cnf_transformation,[],[f72]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4053,plain,
% 23.02/3.51      ( k7_relat_1(X0,X1) = X0
% 23.02/3.51      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 23.02/3.51      | v1_relat_1(X0) != iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_8221,plain,
% 23.02/3.51      ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK4
% 23.02/3.51      | v1_relat_1(sK4) != iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_7038,c_4053]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_12157,plain,
% 23.02/3.51      ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK4 ),
% 23.02/3.51      inference(global_propositional_subsumption,
% 23.02/3.51                [status(thm)],
% 23.02/3.51                [c_8221,c_5270,c_5594,c_6787]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_26272,plain,
% 23.02/3.51      ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4 ),
% 23.02/3.51      inference(light_normalisation,[status(thm)],[c_26270,c_12157]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_25,plain,
% 23.02/3.51      ( ~ sP1(X0,X1,X2,X3,X4)
% 23.02/3.51      | sP0(X4,X3,X2,X1,X0)
% 23.02/3.51      | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
% 23.02/3.51      | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
% 23.02/3.51      | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
% 23.02/3.51      | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
% 23.02/3.51      inference(cnf_transformation,[],[f83]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_35,plain,
% 23.02/3.51      ( sP1(X0,X1,X2,X3,X4)
% 23.02/3.51      | ~ r4_tsep_1(X1,X0,X3)
% 23.02/3.51      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
% 23.02/3.51      | ~ m1_pre_topc(X3,X1)
% 23.02/3.51      | ~ m1_pre_topc(X0,X1)
% 23.02/3.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 23.02/3.51      | v2_struct_0(X1)
% 23.02/3.51      | v2_struct_0(X4)
% 23.02/3.51      | v2_struct_0(X0)
% 23.02/3.51      | v2_struct_0(X3)
% 23.02/3.51      | ~ v2_pre_topc(X4)
% 23.02/3.51      | ~ v2_pre_topc(X1)
% 23.02/3.51      | ~ l1_pre_topc(X1)
% 23.02/3.51      | ~ l1_pre_topc(X4)
% 23.02/3.51      | ~ v1_funct_1(X2) ),
% 23.02/3.51      inference(cnf_transformation,[],[f97]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_69,negated_conjecture,
% 23.02/3.51      ( r4_tsep_1(sK2,sK5,sK6) ),
% 23.02/3.51      inference(cnf_transformation,[],[f112]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_986,plain,
% 23.02/3.51      ( sP1(X0,X1,X2,X3,X4)
% 23.02/3.51      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
% 23.02/3.51      | ~ m1_pre_topc(X0,X1)
% 23.02/3.51      | ~ m1_pre_topc(X3,X1)
% 23.02/3.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 23.02/3.51      | v2_struct_0(X0)
% 23.02/3.51      | v2_struct_0(X1)
% 23.02/3.51      | v2_struct_0(X3)
% 23.02/3.51      | v2_struct_0(X4)
% 23.02/3.51      | ~ v2_pre_topc(X1)
% 23.02/3.51      | ~ v2_pre_topc(X4)
% 23.02/3.51      | ~ l1_pre_topc(X1)
% 23.02/3.51      | ~ l1_pre_topc(X4)
% 23.02/3.51      | ~ v1_funct_1(X2)
% 23.02/3.51      | sK5 != X0
% 23.02/3.51      | sK6 != X3
% 23.02/3.51      | sK2 != X1 ),
% 23.02/3.51      inference(resolution_lifted,[status(thm)],[c_35,c_69]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_987,plain,
% 23.02/3.51      ( sP1(sK5,sK2,X0,sK6,X1)
% 23.02/3.51      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 23.02/3.51      | ~ m1_pre_topc(sK5,sK2)
% 23.02/3.51      | ~ m1_pre_topc(sK6,sK2)
% 23.02/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 23.02/3.51      | v2_struct_0(X1)
% 23.02/3.51      | v2_struct_0(sK5)
% 23.02/3.51      | v2_struct_0(sK6)
% 23.02/3.51      | v2_struct_0(sK2)
% 23.02/3.51      | ~ v2_pre_topc(X1)
% 23.02/3.51      | ~ v2_pre_topc(sK2)
% 23.02/3.51      | ~ l1_pre_topc(X1)
% 23.02/3.51      | ~ l1_pre_topc(sK2)
% 23.02/3.51      | ~ v1_funct_1(X0) ),
% 23.02/3.51      inference(unflattening,[status(thm)],[c_986]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_991,plain,
% 23.02/3.51      ( ~ l1_pre_topc(X1)
% 23.02/3.51      | v2_struct_0(X1)
% 23.02/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 23.02/3.51      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 23.02/3.51      | sP1(sK5,sK2,X0,sK6,X1)
% 23.02/3.51      | ~ v2_pre_topc(X1)
% 23.02/3.51      | ~ v1_funct_1(X0) ),
% 23.02/3.51      inference(global_propositional_subsumption,
% 23.02/3.51                [status(thm)],
% 23.02/3.51                [c_987,c_83,c_82,c_81,c_74,c_73,c_72,c_71]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_992,plain,
% 23.02/3.51      ( sP1(sK5,sK2,X0,sK6,X1)
% 23.02/3.51      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 23.02/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 23.02/3.51      | v2_struct_0(X1)
% 23.02/3.51      | ~ v2_pre_topc(X1)
% 23.02/3.51      | ~ l1_pre_topc(X1)
% 23.02/3.51      | ~ v1_funct_1(X0) ),
% 23.02/3.51      inference(renaming,[status(thm)],[c_991]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_1027,plain,
% 23.02/3.51      ( sP0(X0,X1,X2,X3,X4)
% 23.02/3.51      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_tsep_1(X3,X4,X1),X0)
% 23.02/3.51      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 23.02/3.51      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))
% 23.02/3.51      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 23.02/3.51      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))))
% 23.02/3.51      | v2_struct_0(X6)
% 23.02/3.51      | ~ v2_pre_topc(X6)
% 23.02/3.51      | ~ l1_pre_topc(X6)
% 23.02/3.51      | ~ v1_funct_1(X5)
% 23.02/3.51      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)))
% 23.02/3.51      | X5 != X2
% 23.02/3.51      | X6 != X0
% 23.02/3.51      | sK5 != X4
% 23.02/3.51      | sK6 != X1
% 23.02/3.51      | sK2 != X3 ),
% 23.02/3.51      inference(resolution_lifted,[status(thm)],[c_25,c_992]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_1028,plain,
% 23.02/3.51      ( sP0(X0,sK6,X1,sK2,sK5)
% 23.02/3.51      | ~ v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
% 23.02/3.51      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 23.02/3.51      | ~ v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))
% 23.02/3.51      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 23.02/3.51      | ~ m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
% 23.02/3.51      | v2_struct_0(X0)
% 23.02/3.51      | ~ v2_pre_topc(X0)
% 23.02/3.51      | ~ l1_pre_topc(X0)
% 23.02/3.51      | ~ v1_funct_1(X1)
% 23.02/3.51      | ~ v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) ),
% 23.02/3.51      inference(unflattening,[status(thm)],[c_1027]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4010,plain,
% 23.02/3.51      ( sP0(X0,sK6,X1,sK2,sK5) = iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0) != iProver_top
% 23.02/3.51      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0)) != iProver_top
% 23.02/3.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 23.02/3.51      | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0)))) != iProver_top
% 23.02/3.51      | v2_struct_0(X0) = iProver_top
% 23.02/3.51      | v2_pre_topc(X0) != iProver_top
% 23.02/3.51      | l1_pre_topc(X0) != iProver_top
% 23.02/3.51      | v1_funct_1(X1) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) != iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_1028]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4406,plain,
% 23.02/3.51      ( sP0(X0,sK6,X1,sK2,sK5) = iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,X0,X1,sK2),sK2,X0) != iProver_top
% 23.02/3.51      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 23.02/3.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 23.02/3.51      | m1_subset_1(k2_tmap_1(sK2,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 23.02/3.51      | v2_struct_0(X0) = iProver_top
% 23.02/3.51      | v2_pre_topc(X0) != iProver_top
% 23.02/3.51      | l1_pre_topc(X0) != iProver_top
% 23.02/3.51      | v1_funct_1(X1) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,X0,X1,sK2)) != iProver_top ),
% 23.02/3.51      inference(light_normalisation,[status(thm)],[c_4010,c_70]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_28264,plain,
% 23.02/3.51      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 23.02/3.51      | v2_struct_0(sK3) = iProver_top
% 23.02/3.51      | v2_pre_topc(sK3) != iProver_top
% 23.02/3.51      | l1_pre_topc(sK3) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
% 23.02/3.51      | v1_funct_1(sK4) != iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_26272,c_4406]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_28328,plain,
% 23.02/3.51      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 23.02/3.51      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 23.02/3.51      | v2_struct_0(sK3) = iProver_top
% 23.02/3.51      | v2_pre_topc(sK3) != iProver_top
% 23.02/3.51      | l1_pre_topc(sK3) != iProver_top
% 23.02/3.51      | v1_funct_1(sK4) != iProver_top ),
% 23.02/3.51      inference(light_normalisation,[status(thm)],[c_28264,c_26272]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_28449,plain,
% 23.02/3.51      ( sP0(sK3,sK6,sK4,sK2,sK5)
% 23.02/3.51      | ~ v5_pre_topc(sK4,sK2,sK3)
% 23.02/3.51      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 23.02/3.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 23.02/3.51      | v2_struct_0(sK3)
% 23.02/3.51      | ~ v2_pre_topc(sK3)
% 23.02/3.51      | ~ l1_pre_topc(sK3)
% 23.02/3.51      | ~ v1_funct_1(sK4) ),
% 23.02/3.51      inference(predicate_to_equality_rev,[status(thm)],[c_28328]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_21,plain,
% 23.02/3.51      ( ~ sP1(X0,X1,X2,X3,X4)
% 23.02/3.51      | ~ sP0(X4,X3,X2,X1,X0)
% 23.02/3.51      | m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) ),
% 23.02/3.51      inference(cnf_transformation,[],[f87]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_1156,plain,
% 23.02/3.51      ( ~ sP0(X0,X1,X2,X3,X4)
% 23.02/3.51      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 23.02/3.51      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 23.02/3.51      | m1_subset_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))))
% 23.02/3.51      | v2_struct_0(X6)
% 23.02/3.51      | ~ v2_pre_topc(X6)
% 23.02/3.51      | ~ l1_pre_topc(X6)
% 23.02/3.51      | ~ v1_funct_1(X5)
% 23.02/3.51      | X5 != X2
% 23.02/3.51      | X6 != X0
% 23.02/3.51      | sK5 != X4
% 23.02/3.51      | sK6 != X1
% 23.02/3.51      | sK2 != X3 ),
% 23.02/3.51      inference(resolution_lifted,[status(thm)],[c_21,c_992]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_1157,plain,
% 23.02/3.51      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 23.02/3.51      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 23.02/3.51      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 23.02/3.51      | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
% 23.02/3.51      | v2_struct_0(X0)
% 23.02/3.51      | ~ v2_pre_topc(X0)
% 23.02/3.51      | ~ l1_pre_topc(X0)
% 23.02/3.51      | ~ v1_funct_1(X1) ),
% 23.02/3.51      inference(unflattening,[status(thm)],[c_1156]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4006,plain,
% 23.02/3.51      ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
% 23.02/3.51      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 23.02/3.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 23.02/3.51      | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0)))) = iProver_top
% 23.02/3.51      | v2_struct_0(X0) = iProver_top
% 23.02/3.51      | v2_pre_topc(X0) != iProver_top
% 23.02/3.51      | l1_pre_topc(X0) != iProver_top
% 23.02/3.51      | v1_funct_1(X1) != iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_1157]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4331,plain,
% 23.02/3.51      ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
% 23.02/3.51      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 23.02/3.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 23.02/3.51      | m1_subset_1(k2_tmap_1(sK2,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) = iProver_top
% 23.02/3.51      | v2_struct_0(X0) = iProver_top
% 23.02/3.51      | v2_pre_topc(X0) != iProver_top
% 23.02/3.51      | l1_pre_topc(X0) != iProver_top
% 23.02/3.51      | v1_funct_1(X1) != iProver_top ),
% 23.02/3.51      inference(light_normalisation,[status(thm)],[c_4006,c_70]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_38,negated_conjecture,
% 23.02/3.51      ( v5_pre_topc(sK4,sK2,sK3)
% 23.02/3.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 23.02/3.51      inference(cnf_transformation,[],[f143]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4034,plain,
% 23.02/3.51      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 23.02/3.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_26,plain,
% 23.02/3.51      ( sP0(X0,X1,X2,X3,X4)
% 23.02/3.51      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
% 23.02/3.51      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
% 23.02/3.51      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
% 23.02/3.51      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
% 23.02/3.51      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 23.02/3.51      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
% 23.02/3.51      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
% 23.02/3.51      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
% 23.02/3.51      inference(cnf_transformation,[],[f96]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4043,plain,
% 23.02/3.51      ( sP0(X0,X1,X2,X3,X4) = iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) != iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 23.02/3.51      | m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) != iProver_top
% 23.02/3.51      | m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) != iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_9966,plain,
% 23.02/3.51      ( sP0(sK3,X0,sK4,sK2,sK6) = iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_4034,c_4043]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_92,plain,
% 23.02/3.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_75]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_46,negated_conjecture,
% 23.02/3.51      ( v5_pre_topc(sK4,sK2,sK3)
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
% 23.02/3.51      inference(cnf_transformation,[],[f135]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_120,plain,
% 23.02/3.51      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_42,negated_conjecture,
% 23.02/3.51      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) ),
% 23.02/3.51      inference(cnf_transformation,[],[f139]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_124,plain,
% 23.02/3.51      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_13,plain,
% 23.02/3.51      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 23.02/3.51      inference(cnf_transformation,[],[f75]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_187,plain,
% 23.02/3.51      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_189,plain,
% 23.02/3.51      ( l1_pre_topc(sK3) != iProver_top
% 23.02/3.51      | l1_struct_0(sK3) = iProver_top ),
% 23.02/3.51      inference(instantiation,[status(thm)],[c_187]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_5058,plain,
% 23.02/3.51      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 23.02/3.51      inference(instantiation,[status(thm)],[c_13]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_5059,plain,
% 23.02/3.51      ( l1_pre_topc(sK2) != iProver_top
% 23.02/3.51      | l1_struct_0(sK2) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_5058]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4026,plain,
% 23.02/3.51      ( m1_pre_topc(sK6,sK2) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_71]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_14,plain,
% 23.02/3.51      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 23.02/3.51      inference(cnf_transformation,[],[f76]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4050,plain,
% 23.02/3.51      ( m1_pre_topc(X0,X1) != iProver_top
% 23.02/3.51      | l1_pre_topc(X1) != iProver_top
% 23.02/3.51      | l1_pre_topc(X0) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_6518,plain,
% 23.02/3.51      ( l1_pre_topc(sK6) = iProver_top
% 23.02/3.51      | l1_pre_topc(sK2) != iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_4026,c_4050]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_6815,plain,
% 23.02/3.51      ( l1_pre_topc(sK6) = iProver_top ),
% 23.02/3.51      inference(global_propositional_subsumption,
% 23.02/3.51                [status(thm)],
% 23.02/3.51                [c_6518,c_86]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4051,plain,
% 23.02/3.51      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_6820,plain,
% 23.02/3.51      ( l1_struct_0(sK6) = iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_6815,c_4051]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_20,plain,
% 23.02/3.51      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.02/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.02/3.51      | ~ l1_struct_0(X3)
% 23.02/3.51      | ~ l1_struct_0(X2)
% 23.02/3.51      | ~ l1_struct_0(X1)
% 23.02/3.51      | ~ v1_funct_1(X0)
% 23.02/3.51      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 23.02/3.51      inference(cnf_transformation,[],[f80]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4679,plain,
% 23.02/3.51      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 23.02/3.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 23.02/3.51      | ~ l1_struct_0(X1)
% 23.02/3.51      | ~ l1_struct_0(X0)
% 23.02/3.51      | ~ l1_struct_0(X2)
% 23.02/3.51      | v1_funct_1(k2_tmap_1(X0,X1,sK4,X2))
% 23.02/3.51      | ~ v1_funct_1(sK4) ),
% 23.02/3.51      inference(instantiation,[status(thm)],[c_20]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4819,plain,
% 23.02/3.51      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 23.02/3.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 23.02/3.51      | ~ l1_struct_0(X0)
% 23.02/3.51      | ~ l1_struct_0(sK3)
% 23.02/3.51      | ~ l1_struct_0(sK2)
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
% 23.02/3.51      | ~ v1_funct_1(sK4) ),
% 23.02/3.51      inference(instantiation,[status(thm)],[c_4679]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_7586,plain,
% 23.02/3.51      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 23.02/3.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 23.02/3.51      | ~ l1_struct_0(sK6)
% 23.02/3.51      | ~ l1_struct_0(sK3)
% 23.02/3.51      | ~ l1_struct_0(sK2)
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 23.02/3.51      | ~ v1_funct_1(sK4) ),
% 23.02/3.51      inference(instantiation,[status(thm)],[c_4819]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_7587,plain,
% 23.02/3.51      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 23.02/3.51      | l1_struct_0(sK6) != iProver_top
% 23.02/3.51      | l1_struct_0(sK3) != iProver_top
% 23.02/3.51      | l1_struct_0(sK2) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top
% 23.02/3.51      | v1_funct_1(sK4) != iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_7586]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_10542,plain,
% 23.02/3.51      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
% 23.02/3.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
% 23.02/3.51      | sP0(sK3,X0,sK4,sK2,sK6) = iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top ),
% 23.02/3.51      inference(global_propositional_subsumption,
% 23.02/3.51                [status(thm)],
% 23.02/3.51                [c_9966,c_86,c_89,c_90,c_91,c_92,c_120,c_124,c_189,
% 23.02/3.51                 c_5059,c_6820,c_7587]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_10543,plain,
% 23.02/3.51      ( sP0(sK3,X0,sK4,sK2,sK6) = iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top ),
% 23.02/3.51      inference(renaming,[status(thm)],[c_10542]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_10557,plain,
% 23.02/3.51      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 23.02/3.51      | sP0(sK3,sK2,sK4,sK2,sK6) = iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 23.02/3.51      | v2_struct_0(sK3) = iProver_top
% 23.02/3.51      | v2_pre_topc(sK3) != iProver_top
% 23.02/3.51      | l1_pre_topc(sK3) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
% 23.02/3.51      | v1_funct_1(sK4) != iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_4331,c_10543]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_22,plain,
% 23.02/3.51      ( ~ sP1(X0,X1,X2,X3,X4)
% 23.02/3.51      | ~ sP0(X4,X3,X2,X1,X0)
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) ),
% 23.02/3.51      inference(cnf_transformation,[],[f86]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_1126,plain,
% 23.02/3.51      ( ~ sP0(X0,X1,X2,X3,X4)
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_tsep_1(X3,X4,X1),X0)
% 23.02/3.51      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 23.02/3.51      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 23.02/3.51      | v2_struct_0(X6)
% 23.02/3.51      | ~ v2_pre_topc(X6)
% 23.02/3.51      | ~ l1_pre_topc(X6)
% 23.02/3.51      | ~ v1_funct_1(X5)
% 23.02/3.51      | X5 != X2
% 23.02/3.51      | X6 != X0
% 23.02/3.51      | sK5 != X4
% 23.02/3.51      | sK6 != X1
% 23.02/3.51      | sK2 != X3 ),
% 23.02/3.51      inference(resolution_lifted,[status(thm)],[c_22,c_992]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_1127,plain,
% 23.02/3.51      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
% 23.02/3.51      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 23.02/3.51      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 23.02/3.51      | v2_struct_0(X0)
% 23.02/3.51      | ~ v2_pre_topc(X0)
% 23.02/3.51      | ~ l1_pre_topc(X0)
% 23.02/3.51      | ~ v1_funct_1(X1) ),
% 23.02/3.51      inference(unflattening,[status(thm)],[c_1126]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4007,plain,
% 23.02/3.51      ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0) = iProver_top
% 23.02/3.51      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 23.02/3.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 23.02/3.51      | v2_struct_0(X0) = iProver_top
% 23.02/3.51      | v2_pre_topc(X0) != iProver_top
% 23.02/3.51      | l1_pre_topc(X0) != iProver_top
% 23.02/3.51      | v1_funct_1(X1) != iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_1127]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4297,plain,
% 23.02/3.51      ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,X0,X1,sK2),sK2,X0) = iProver_top
% 23.02/3.51      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 23.02/3.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 23.02/3.51      | v2_struct_0(X0) = iProver_top
% 23.02/3.51      | v2_pre_topc(X0) != iProver_top
% 23.02/3.51      | l1_pre_topc(X0) != iProver_top
% 23.02/3.51      | v1_funct_1(X1) != iProver_top ),
% 23.02/3.51      inference(light_normalisation,[status(thm)],[c_4007,c_70]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_5463,plain,
% 23.02/3.51      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
% 23.02/3.51      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | v2_struct_0(sK3) = iProver_top
% 23.02/3.51      | v2_pre_topc(sK3) != iProver_top
% 23.02/3.51      | l1_pre_topc(sK3) != iProver_top
% 23.02/3.51      | v1_funct_1(sK4) != iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_4022,c_4297]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_8969,plain,
% 23.02/3.51      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
% 23.02/3.51      | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top ),
% 23.02/3.51      inference(global_propositional_subsumption,
% 23.02/3.51                [status(thm)],
% 23.02/3.51                [c_5463,c_87,c_88,c_89,c_90,c_91]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_8970,plain,
% 23.02/3.51      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top ),
% 23.02/3.51      inference(renaming,[status(thm)],[c_8969]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_19,plain,
% 23.02/3.51      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.02/3.51      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 23.02/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.02/3.51      | ~ l1_struct_0(X3)
% 23.02/3.51      | ~ l1_struct_0(X2)
% 23.02/3.51      | ~ l1_struct_0(X1)
% 23.02/3.51      | ~ v1_funct_1(X0) ),
% 23.02/3.51      inference(cnf_transformation,[],[f81]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4689,plain,
% 23.02/3.51      ( v1_funct_2(k2_tmap_1(X0,X1,sK4,X2),u1_struct_0(X2),u1_struct_0(X1))
% 23.02/3.51      | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 23.02/3.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 23.02/3.51      | ~ l1_struct_0(X1)
% 23.02/3.51      | ~ l1_struct_0(X0)
% 23.02/3.51      | ~ l1_struct_0(X2)
% 23.02/3.51      | ~ v1_funct_1(sK4) ),
% 23.02/3.51      inference(instantiation,[status(thm)],[c_19]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4829,plain,
% 23.02/3.51      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
% 23.02/3.51      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 23.02/3.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 23.02/3.51      | ~ l1_struct_0(X0)
% 23.02/3.51      | ~ l1_struct_0(sK3)
% 23.02/3.51      | ~ l1_struct_0(sK2)
% 23.02/3.51      | ~ v1_funct_1(sK4) ),
% 23.02/3.51      inference(instantiation,[status(thm)],[c_4689]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_10842,plain,
% 23.02/3.51      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
% 23.02/3.51      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 23.02/3.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 23.02/3.51      | ~ l1_struct_0(sK3)
% 23.02/3.51      | ~ l1_struct_0(sK2)
% 23.02/3.51      | ~ v1_funct_1(sK4) ),
% 23.02/3.51      inference(instantiation,[status(thm)],[c_4829]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_10845,plain,
% 23.02/3.51      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
% 23.02/3.51      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 23.02/3.51      | l1_struct_0(sK3) != iProver_top
% 23.02/3.51      | l1_struct_0(sK2) != iProver_top
% 23.02/3.51      | v1_funct_1(sK4) != iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_10842]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_54,negated_conjecture,
% 23.02/3.51      ( v5_pre_topc(sK4,sK2,sK3)
% 23.02/3.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 23.02/3.51      inference(cnf_transformation,[],[f127]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4030,plain,
% 23.02/3.51      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 23.02/3.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_9967,plain,
% 23.02/3.51      ( sP0(sK3,X0,sK4,sK2,sK5) = iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_4030,c_4043]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_62,negated_conjecture,
% 23.02/3.51      ( v5_pre_topc(sK4,sK2,sK3)
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 23.02/3.51      inference(cnf_transformation,[],[f119]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_104,plain,
% 23.02/3.51      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_58,negated_conjecture,
% 23.02/3.51      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) ),
% 23.02/3.51      inference(cnf_transformation,[],[f123]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_108,plain,
% 23.02/3.51      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_5894,plain,
% 23.02/3.51      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 23.02/3.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 23.02/3.51      | ~ l1_struct_0(sK5)
% 23.02/3.51      | ~ l1_struct_0(sK3)
% 23.02/3.51      | ~ l1_struct_0(sK2)
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 23.02/3.51      | ~ v1_funct_1(sK4) ),
% 23.02/3.51      inference(instantiation,[status(thm)],[c_4819]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_5895,plain,
% 23.02/3.51      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 23.02/3.51      | l1_struct_0(sK5) != iProver_top
% 23.02/3.51      | l1_struct_0(sK3) != iProver_top
% 23.02/3.51      | l1_struct_0(sK2) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top
% 23.02/3.51      | v1_funct_1(sK4) != iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_5894]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4024,plain,
% 23.02/3.51      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_73]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_6519,plain,
% 23.02/3.51      ( l1_pre_topc(sK5) = iProver_top
% 23.02/3.51      | l1_pre_topc(sK2) != iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_4024,c_4050]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_7030,plain,
% 23.02/3.51      ( l1_pre_topc(sK5) = iProver_top ),
% 23.02/3.51      inference(global_propositional_subsumption,
% 23.02/3.51                [status(thm)],
% 23.02/3.51                [c_6519,c_86]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_7035,plain,
% 23.02/3.51      ( l1_struct_0(sK5) = iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_7030,c_4051]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_10692,plain,
% 23.02/3.51      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
% 23.02/3.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
% 23.02/3.51      | sP0(sK3,X0,sK4,sK2,sK5) = iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top ),
% 23.02/3.51      inference(global_propositional_subsumption,
% 23.02/3.51                [status(thm)],
% 23.02/3.51                [c_9967,c_86,c_89,c_90,c_91,c_92,c_104,c_108,c_189,
% 23.02/3.51                 c_5059,c_5895,c_7035]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_10693,plain,
% 23.02/3.51      ( sP0(sK3,X0,sK4,sK2,sK5) = iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top ),
% 23.02/3.51      inference(renaming,[status(thm)],[c_10692]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_10705,plain,
% 23.02/3.51      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_4034,c_10693]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_11011,plain,
% 23.02/3.51      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 23.02/3.51      inference(global_propositional_subsumption,
% 23.02/3.51                [status(thm)],
% 23.02/3.51                [c_10705,c_86,c_89,c_90,c_91,c_92,c_120,c_124,c_189,
% 23.02/3.51                 c_5059,c_6820,c_7587]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_24,plain,
% 23.02/3.51      ( ~ sP1(X0,X1,X2,X3,X4)
% 23.02/3.51      | ~ sP0(X4,X3,X2,X1,X0)
% 23.02/3.51      | v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
% 23.02/3.51      inference(cnf_transformation,[],[f84]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_1066,plain,
% 23.02/3.51      ( ~ sP0(X0,X1,X2,X3,X4)
% 23.02/3.51      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 23.02/3.51      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 23.02/3.51      | v2_struct_0(X6)
% 23.02/3.51      | ~ v2_pre_topc(X6)
% 23.02/3.51      | ~ l1_pre_topc(X6)
% 23.02/3.51      | ~ v1_funct_1(X5)
% 23.02/3.51      | v1_funct_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)))
% 23.02/3.51      | X5 != X2
% 23.02/3.51      | X6 != X0
% 23.02/3.51      | sK5 != X4
% 23.02/3.51      | sK6 != X1
% 23.02/3.51      | sK2 != X3 ),
% 23.02/3.51      inference(resolution_lifted,[status(thm)],[c_24,c_992]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_1067,plain,
% 23.02/3.51      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 23.02/3.51      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 23.02/3.51      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 23.02/3.51      | v2_struct_0(X0)
% 23.02/3.51      | ~ v2_pre_topc(X0)
% 23.02/3.51      | ~ l1_pre_topc(X0)
% 23.02/3.51      | ~ v1_funct_1(X1)
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) ),
% 23.02/3.51      inference(unflattening,[status(thm)],[c_1066]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4009,plain,
% 23.02/3.51      ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
% 23.02/3.51      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 23.02/3.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 23.02/3.51      | v2_struct_0(X0) = iProver_top
% 23.02/3.51      | v2_pre_topc(X0) != iProver_top
% 23.02/3.51      | l1_pre_topc(X0) != iProver_top
% 23.02/3.51      | v1_funct_1(X1) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_1067]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4280,plain,
% 23.02/3.51      ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
% 23.02/3.51      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 23.02/3.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 23.02/3.51      | v2_struct_0(X0) = iProver_top
% 23.02/3.51      | v2_pre_topc(X0) != iProver_top
% 23.02/3.51      | l1_pre_topc(X0) != iProver_top
% 23.02/3.51      | v1_funct_1(X1) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,X0,X1,sK2)) = iProver_top ),
% 23.02/3.51      inference(light_normalisation,[status(thm)],[c_4009,c_70]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_5452,plain,
% 23.02/3.51      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 23.02/3.51      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | v2_struct_0(sK3) = iProver_top
% 23.02/3.51      | v2_pre_topc(sK3) != iProver_top
% 23.02/3.51      | l1_pre_topc(sK3) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top
% 23.02/3.51      | v1_funct_1(sK4) != iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_4022,c_4280]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_8962,plain,
% 23.02/3.51      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top
% 23.02/3.51      | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top ),
% 23.02/3.51      inference(global_propositional_subsumption,
% 23.02/3.51                [status(thm)],
% 23.02/3.51                [c_5452,c_87,c_88,c_89,c_90,c_91]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_8963,plain,
% 23.02/3.51      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top ),
% 23.02/3.51      inference(renaming,[status(thm)],[c_8962]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_11026,plain,
% 23.02/3.51      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_11011,c_8963]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_11904,plain,
% 23.02/3.51      ( sP0(sK3,sK2,sK4,sK2,sK6) = iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 23.02/3.51      inference(global_propositional_subsumption,
% 23.02/3.51                [status(thm)],
% 23.02/3.51                [c_10557,c_86,c_87,c_88,c_89,c_90,c_91,c_92,c_189,c_5059,
% 23.02/3.51                 c_8970,c_10845,c_11011,c_11026]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4041,plain,
% 23.02/3.51      ( sP0(X0,X1,X2,X3,X4) != iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) = iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_11913,plain,
% 23.02/3.51      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_11904,c_4041]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_28219,plain,
% 23.02/3.51      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 23.02/3.51      inference(demodulation,[status(thm)],[c_26272,c_11913]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_28246,plain,
% 23.02/3.51      ( v5_pre_topc(sK4,sK2,sK3) ),
% 23.02/3.51      inference(predicate_to_equality_rev,[status(thm)],[c_28219]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4045,plain,
% 23.02/3.51      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2)) = iProver_top
% 23.02/3.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 23.02/3.51      | l1_struct_0(X3) != iProver_top
% 23.02/3.51      | l1_struct_0(X2) != iProver_top
% 23.02/3.51      | l1_struct_0(X1) != iProver_top
% 23.02/3.51      | v1_funct_1(X0) != iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4056,plain,
% 23.02/3.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 23.02/3.51      | r1_tarski(X0,X1) != iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_18,plain,
% 23.02/3.51      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.02/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.02/3.51      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 23.02/3.51      | ~ l1_struct_0(X3)
% 23.02/3.51      | ~ l1_struct_0(X2)
% 23.02/3.51      | ~ l1_struct_0(X1)
% 23.02/3.51      | ~ v1_funct_1(X0) ),
% 23.02/3.51      inference(cnf_transformation,[],[f82]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4046,plain,
% 23.02/3.51      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 23.02/3.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 23.02/3.51      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) = iProver_top
% 23.02/3.51      | l1_struct_0(X3) != iProver_top
% 23.02/3.51      | l1_struct_0(X2) != iProver_top
% 23.02/3.51      | l1_struct_0(X1) != iProver_top
% 23.02/3.51      | v1_funct_1(X0) != iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_36,negated_conjecture,
% 23.02/3.51      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 23.02/3.51      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 23.02/3.51      | ~ v5_pre_topc(sK4,sK2,sK3)
% 23.02/3.51      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 23.02/3.51      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 23.02/3.51      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 23.02/3.51      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 23.02/3.51      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 23.02/3.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 23.02/3.51      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 23.02/3.51      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 23.02/3.51      | ~ v1_funct_1(sK4) ),
% 23.02/3.51      inference(cnf_transformation,[],[f145]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_532,plain,
% 23.02/3.51      ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 23.02/3.51      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 23.02/3.51      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 23.02/3.51      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 23.02/3.51      | ~ v5_pre_topc(sK4,sK2,sK3)
% 23.02/3.51      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 23.02/3.51      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 23.02/3.51      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 23.02/3.51      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 23.02/3.51      inference(global_propositional_subsumption,
% 23.02/3.51                [status(thm)],
% 23.02/3.51                [c_36,c_77,c_76,c_75]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_533,negated_conjecture,
% 23.02/3.51      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 23.02/3.51      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 23.02/3.51      | ~ v5_pre_topc(sK4,sK2,sK3)
% 23.02/3.51      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 23.02/3.51      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 23.02/3.51      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 23.02/3.51      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 23.02/3.51      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 23.02/3.51      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 23.02/3.51      inference(renaming,[status(thm)],[c_532]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_4013,plain,
% 23.02/3.51      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 23.02/3.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 23.02/3.51      inference(predicate_to_equality,[status(thm)],[c_533]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_11053,plain,
% 23.02/3.51      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 23.02/3.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 23.02/3.51      | l1_struct_0(sK5) != iProver_top
% 23.02/3.51      | l1_struct_0(sK3) != iProver_top
% 23.02/3.51      | l1_struct_0(sK2) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 23.02/3.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top
% 23.02/3.51      | v1_funct_1(sK4) != iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_4046,c_4013]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_11657,plain,
% 23.02/3.51      ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top ),
% 23.02/3.51      inference(global_propositional_subsumption,
% 23.02/3.51                [status(thm)],
% 23.02/3.51                [c_11053,c_86,c_89,c_90,c_91,c_92,c_189,c_5059,c_5895,
% 23.02/3.51                 c_6820,c_7035,c_7587]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_11658,plain,
% 23.02/3.51      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top ),
% 23.02/3.51      inference(renaming,[status(thm)],[c_11657]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_11667,plain,
% 23.02/3.51      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | r1_tarski(k2_tmap_1(sK2,sK3,sK4,sK6),k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))) != iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_4056,c_11658]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_11668,plain,
% 23.02/3.51      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 23.02/3.51      | l1_struct_0(sK6) != iProver_top
% 23.02/3.51      | l1_struct_0(sK3) != iProver_top
% 23.02/3.51      | l1_struct_0(sK2) != iProver_top
% 23.02/3.51      | v1_funct_1(sK4) != iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_4046,c_11658]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_13416,plain,
% 23.02/3.51      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top ),
% 23.02/3.51      inference(global_propositional_subsumption,
% 23.02/3.51                [status(thm)],
% 23.02/3.51                [c_11667,c_86,c_89,c_90,c_91,c_92,c_189,c_5059,c_6820,
% 23.02/3.51                 c_11668]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_13417,plain,
% 23.02/3.51      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top ),
% 23.02/3.51      inference(renaming,[status(thm)],[c_13416]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_13425,plain,
% 23.02/3.51      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 23.02/3.51      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 23.02/3.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.02/3.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 23.02/3.51      | l1_struct_0(sK5) != iProver_top
% 23.02/3.51      | l1_struct_0(sK3) != iProver_top
% 23.02/3.51      | l1_struct_0(sK2) != iProver_top
% 23.02/3.51      | v1_funct_1(sK4) != iProver_top ),
% 23.02/3.51      inference(superposition,[status(thm)],[c_4045,c_13417]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_13447,plain,
% 23.02/3.51      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 23.02/3.51      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 23.02/3.51      | ~ v5_pre_topc(sK4,sK2,sK3)
% 23.02/3.51      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 23.02/3.51      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 23.02/3.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 23.02/3.51      | ~ l1_struct_0(sK5)
% 23.02/3.51      | ~ l1_struct_0(sK3)
% 23.02/3.51      | ~ l1_struct_0(sK2)
% 23.02/3.51      | ~ v1_funct_1(sK4) ),
% 23.02/3.51      inference(predicate_to_equality_rev,[status(thm)],[c_13425]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_7036,plain,
% 23.02/3.51      ( l1_struct_0(sK5) ),
% 23.02/3.51      inference(predicate_to_equality_rev,[status(thm)],[c_7035]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(c_188,plain,
% 23.02/3.51      ( ~ l1_pre_topc(sK3) | l1_struct_0(sK3) ),
% 23.02/3.51      inference(instantiation,[status(thm)],[c_13]) ).
% 23.02/3.51  
% 23.02/3.51  cnf(contradiction,plain,
% 23.02/3.51      ( $false ),
% 23.02/3.51      inference(minisat,
% 23.02/3.51                [status(thm)],
% 23.02/3.51                [c_74495,c_74487,c_74483,c_28449,c_28246,c_13447,c_7036,
% 23.02/3.51                 c_5058,c_188,c_75,c_76,c_77,c_78,c_79,c_80,c_81]) ).
% 23.02/3.51  
% 23.02/3.51  
% 23.02/3.51  % SZS output end CNFRefutation for theBenchmark.p
% 23.02/3.51  
% 23.02/3.51  ------                               Statistics
% 23.02/3.51  
% 23.02/3.51  ------ General
% 23.02/3.51  
% 23.02/3.51  abstr_ref_over_cycles:                  0
% 23.02/3.51  abstr_ref_under_cycles:                 0
% 23.02/3.51  gc_basic_clause_elim:                   0
% 23.02/3.51  forced_gc_time:                         0
% 23.02/3.51  parsing_time:                           0.01
% 23.02/3.51  unif_index_cands_time:                  0.
% 23.02/3.51  unif_index_add_time:                    0.
% 23.02/3.51  orderings_time:                         0.
% 23.02/3.51  out_proof_time:                         0.034
% 23.02/3.51  total_time:                             2.521
% 23.02/3.51  num_of_symbols:                         59
% 23.02/3.51  num_of_terms:                           73312
% 23.02/3.51  
% 23.02/3.51  ------ Preprocessing
% 23.02/3.51  
% 23.02/3.51  num_of_splits:                          0
% 23.02/3.51  num_of_split_atoms:                     0
% 23.02/3.51  num_of_reused_defs:                     0
% 23.02/3.51  num_eq_ax_congr_red:                    34
% 23.02/3.51  num_of_sem_filtered_clauses:            1
% 23.02/3.51  num_of_subtypes:                        0
% 23.02/3.51  monotx_restored_types:                  0
% 23.02/3.51  sat_num_of_epr_types:                   0
% 23.02/3.51  sat_num_of_non_cyclic_types:            0
% 23.02/3.51  sat_guarded_non_collapsed_types:        0
% 23.02/3.51  num_pure_diseq_elim:                    0
% 23.02/3.51  simp_replaced_by:                       0
% 23.02/3.51  res_preprocessed:                       263
% 23.02/3.51  prep_upred:                             0
% 23.02/3.51  prep_unflattend:                        148
% 23.02/3.51  smt_new_axioms:                         0
% 23.02/3.51  pred_elim_cands:                        12
% 23.02/3.51  pred_elim:                              3
% 23.02/3.51  pred_elim_cl:                           4
% 23.02/3.51  pred_elim_cycles:                       5
% 23.02/3.51  merged_defs:                            8
% 23.02/3.51  merged_defs_ncl:                        0
% 23.02/3.51  bin_hyper_res:                          9
% 23.02/3.51  prep_cycles:                            4
% 23.02/3.51  pred_elim_time:                         0.046
% 23.02/3.51  splitting_time:                         0.
% 23.02/3.51  sem_filter_time:                        0.
% 23.02/3.51  monotx_time:                            0.001
% 23.02/3.51  subtype_inf_time:                       0.
% 23.02/3.51  
% 23.02/3.51  ------ Problem properties
% 23.02/3.51  
% 23.02/3.51  clauses:                                55
% 23.02/3.51  conjectures:                            23
% 23.02/3.51  epr:                                    17
% 23.02/3.51  horn:                                   39
% 23.02/3.51  ground:                                 23
% 23.02/3.51  unary:                                  16
% 23.02/3.51  binary:                                 19
% 23.02/3.51  lits:                                   182
% 23.02/3.51  lits_eq:                                5
% 23.02/3.51  fd_pure:                                0
% 23.02/3.51  fd_pseudo:                              0
% 23.02/3.51  fd_cond:                                0
% 23.02/3.51  fd_pseudo_cond:                         1
% 23.02/3.51  ac_symbols:                             0
% 23.02/3.51  
% 23.02/3.51  ------ Propositional Solver
% 23.02/3.51  
% 23.02/3.51  prop_solver_calls:                      33
% 23.02/3.51  prop_fast_solver_calls:                 5498
% 23.02/3.51  smt_solver_calls:                       0
% 23.02/3.51  smt_fast_solver_calls:                  0
% 23.02/3.51  prop_num_of_clauses:                    22260
% 23.02/3.51  prop_preprocess_simplified:             35468
% 23.02/3.51  prop_fo_subsumed:                       750
% 23.02/3.51  prop_solver_time:                       0.
% 23.02/3.51  smt_solver_time:                        0.
% 23.02/3.51  smt_fast_solver_time:                   0.
% 23.02/3.51  prop_fast_solver_time:                  0.
% 23.02/3.51  prop_unsat_core_time:                   0.004
% 23.02/3.51  
% 23.02/3.51  ------ QBF
% 23.02/3.51  
% 23.02/3.51  qbf_q_res:                              0
% 23.02/3.51  qbf_num_tautologies:                    0
% 23.02/3.51  qbf_prep_cycles:                        0
% 23.02/3.51  
% 23.02/3.51  ------ BMC1
% 23.02/3.51  
% 23.02/3.51  bmc1_current_bound:                     -1
% 23.02/3.51  bmc1_last_solved_bound:                 -1
% 23.02/3.51  bmc1_unsat_core_size:                   -1
% 23.02/3.51  bmc1_unsat_core_parents_size:           -1
% 23.02/3.51  bmc1_merge_next_fun:                    0
% 23.02/3.51  bmc1_unsat_core_clauses_time:           0.
% 23.02/3.51  
% 23.02/3.51  ------ Instantiation
% 23.02/3.51  
% 23.02/3.51  inst_num_of_clauses:                    5200
% 23.02/3.51  inst_num_in_passive:                    1041
% 23.02/3.51  inst_num_in_active:                     2545
% 23.02/3.51  inst_num_in_unprocessed:                1613
% 23.02/3.51  inst_num_of_loops:                      2638
% 23.02/3.51  inst_num_of_learning_restarts:          0
% 23.02/3.51  inst_num_moves_active_passive:          89
% 23.02/3.51  inst_lit_activity:                      0
% 23.02/3.51  inst_lit_activity_moves:                2
% 23.02/3.51  inst_num_tautologies:                   0
% 23.02/3.51  inst_num_prop_implied:                  0
% 23.02/3.51  inst_num_existing_simplified:           0
% 23.02/3.51  inst_num_eq_res_simplified:             0
% 23.02/3.51  inst_num_child_elim:                    0
% 23.02/3.51  inst_num_of_dismatching_blockings:      6186
% 23.02/3.51  inst_num_of_non_proper_insts:           7990
% 23.02/3.51  inst_num_of_duplicates:                 0
% 23.02/3.51  inst_inst_num_from_inst_to_res:         0
% 23.02/3.51  inst_dismatching_checking_time:         0.
% 23.02/3.51  
% 23.02/3.51  ------ Resolution
% 23.02/3.51  
% 23.02/3.51  res_num_of_clauses:                     0
% 23.02/3.51  res_num_in_passive:                     0
% 23.02/3.51  res_num_in_active:                      0
% 23.02/3.51  res_num_of_loops:                       267
% 23.02/3.51  res_forward_subset_subsumed:            93
% 23.02/3.51  res_backward_subset_subsumed:           0
% 23.02/3.51  res_forward_subsumed:                   0
% 23.02/3.51  res_backward_subsumed:                  0
% 23.02/3.51  res_forward_subsumption_resolution:     0
% 23.02/3.51  res_backward_subsumption_resolution:    0
% 23.02/3.51  res_clause_to_clause_subsumption:       8425
% 23.02/3.51  res_orphan_elimination:                 0
% 23.02/3.51  res_tautology_del:                      185
% 23.02/3.51  res_num_eq_res_simplified:              0
% 23.02/3.51  res_num_sel_changes:                    0
% 23.02/3.51  res_moves_from_active_to_pass:          0
% 23.02/3.51  
% 23.02/3.51  ------ Superposition
% 23.02/3.51  
% 23.02/3.51  sup_time_total:                         0.
% 23.02/3.51  sup_time_generating:                    0.
% 23.02/3.51  sup_time_sim_full:                      0.
% 23.02/3.51  sup_time_sim_immed:                     0.
% 23.02/3.51  
% 23.02/3.51  sup_num_of_clauses:                     1905
% 23.02/3.51  sup_num_in_active:                      460
% 23.02/3.51  sup_num_in_passive:                     1445
% 23.02/3.51  sup_num_of_loops:                       526
% 23.02/3.51  sup_fw_superposition:                   1044
% 23.02/3.51  sup_bw_superposition:                   1522
% 23.02/3.51  sup_immediate_simplified:               807
% 23.02/3.51  sup_given_eliminated:                   0
% 23.02/3.51  comparisons_done:                       0
% 23.02/3.51  comparisons_avoided:                    0
% 23.02/3.51  
% 23.02/3.51  ------ Simplifications
% 23.02/3.51  
% 23.02/3.51  
% 23.02/3.51  sim_fw_subset_subsumed:                 172
% 23.02/3.51  sim_bw_subset_subsumed:                 56
% 23.02/3.51  sim_fw_subsumed:                        52
% 23.02/3.51  sim_bw_subsumed:                        4
% 23.02/3.51  sim_fw_subsumption_res:                 15
% 23.02/3.51  sim_bw_subsumption_res:                 3
% 23.02/3.51  sim_tautology_del:                      22
% 23.02/3.51  sim_eq_tautology_del:                   24
% 23.02/3.51  sim_eq_res_simp:                        0
% 23.02/3.51  sim_fw_demodulated:                     8
% 23.02/3.51  sim_bw_demodulated:                     63
% 23.02/3.51  sim_light_normalised:                   615
% 23.02/3.51  sim_joinable_taut:                      0
% 23.02/3.51  sim_joinable_simp:                      0
% 23.02/3.51  sim_ac_normalised:                      0
% 23.02/3.51  sim_smt_subsumption:                    0
% 23.02/3.51  
%------------------------------------------------------------------------------
