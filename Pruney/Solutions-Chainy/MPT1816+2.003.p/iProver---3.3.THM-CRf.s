%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:19 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  288 (16834 expanded)
%              Number of clauses        :  199 (3660 expanded)
%              Number of leaves         :   21 (5910 expanded)
%              Depth                    :   27
%              Number of atoms          : 1888 (530512 expanded)
%              Number of equality atoms :  485 (21048 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   78 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f31])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f32])).

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
    inference(flattening,[],[f42])).

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f49,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f43,f48,f47,f46,f45,f44])).

fof(f90,plain,(
    k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
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
    inference(pure_predicate_removal,[],[f8])).

fof(f25,plain,(
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
    inference(flattening,[],[f25])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f77,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f86,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f87,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f88,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f89,plain,(
    m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f85,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f49])).

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
                  ( m1_pre_topc(X3,X0)
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f7])).

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
    inference(flattening,[],[f23])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f78,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f82,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
      <=> sP0(X1,X3,X4,X0,X2) )
      | ~ sP1(X2,X0,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f34])).

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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0)
      | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
      | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
      | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f29])).

fof(f33,plain,(
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

fof(f35,plain,(
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
    inference(definition_folding,[],[f30,f34,f33])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,(
    r4_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f27])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f98,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f102,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f106,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f114,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f118,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f122,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f33])).

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
    inference(flattening,[],[f39])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f124,plain,
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
    inference(cnf_transformation,[],[f49])).

cnf(c_61,negated_conjecture,
    ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2373,negated_conjecture,
    ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(subtyping,[status(esa)],[c_61])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2395,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X2_54,X1_54)
    | m1_pre_topc(k1_tsep_1(X1_54,X0_54,X2_54),X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3249,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1_54,X0_54,X2_54),X1_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2395])).

cnf(c_5467,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2373,c_3249])).

cnf(c_74,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_75,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_74])).

cnf(c_72,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_77,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_72])).

cnf(c_65,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_84,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65])).

cnf(c_64,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_85,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64])).

cnf(c_63,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_86,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63])).

cnf(c_62,negated_conjecture,
    ( m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_87,plain,
    ( m1_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_3430,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | m1_pre_topc(k1_tsep_1(X1_54,sK5,X0_54),X1_54)
    | ~ m1_pre_topc(sK5,X1_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(X1_54) ),
    inference(instantiation,[status(thm)],[c_2395])).

cnf(c_3579,plain,
    ( ~ m1_pre_topc(X0_54,sK2)
    | m1_pre_topc(k1_tsep_1(sK2,sK5,X0_54),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3430])).

cnf(c_3848,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3579])).

cnf(c_3849,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3848])).

cnf(c_2401,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_3913,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_2401])).

cnf(c_2406,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_3759,plain,
    ( X0_54 != X1_54
    | sK2 != X1_54
    | sK2 = X0_54 ),
    inference(instantiation,[status(thm)],[c_2406])).

cnf(c_3915,plain,
    ( X0_54 != sK2
    | sK2 = X0_54
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3759])).

cnf(c_4347,plain,
    ( k1_tsep_1(sK2,sK5,sK6) != sK2
    | sK2 = k1_tsep_1(sK2,sK5,sK6)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3915])).

cnf(c_2414,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | m1_pre_topc(X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_3601,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | m1_pre_topc(X2_54,sK2)
    | X2_54 != X0_54
    | sK2 != X1_54 ),
    inference(instantiation,[status(thm)],[c_2414])).

cnf(c_3790,plain,
    ( ~ m1_pre_topc(X0_54,sK2)
    | m1_pre_topc(X1_54,sK2)
    | X1_54 != X0_54
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3601])).

cnf(c_4279,plain,
    ( m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2)
    | X0_54 != k1_tsep_1(sK2,sK5,sK6)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3790])).

cnf(c_5007,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2)
    | m1_pre_topc(sK2,sK2)
    | sK2 != k1_tsep_1(sK2,sK5,sK6)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4279])).

cnf(c_5008,plain,
    ( sK2 != k1_tsep_1(sK2,sK5,sK6)
    | sK2 != sK2
    | m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5007])).

cnf(c_6222,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5467,c_75,c_77,c_84,c_85,c_86,c_87,c_2373,c_3849,c_3913,c_4347,c_5008])).

cnf(c_66,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2368,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_66])).

cnf(c_3275,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2368])).

cnf(c_6,plain,
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
    inference(cnf_transformation,[],[f56])).

cnf(c_2396,plain,
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
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3248,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_2396])).

cnf(c_4542,plain,
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
    inference(superposition,[status(thm)],[c_3275,c_3248])).

cnf(c_73,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_76,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_71,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_78,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_70,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_79,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_70])).

cnf(c_69,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_80,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_68,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_81,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_68])).

cnf(c_67,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_82,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_67])).

cnf(c_6437,plain,
    ( m1_pre_topc(X0_54,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK3,sK4,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4542,c_75,c_76,c_77,c_78,c_79,c_80,c_81,c_82])).

cnf(c_6438,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK3,sK4,X0_54)
    | m1_pre_topc(X0_54,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6437])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2399,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_funct_1(X0_55)
    | k2_partfun1(X0_56,X1_56,X0_55,X2_56) = k7_relat_1(X0_55,X2_56) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_3245,plain,
    ( k2_partfun1(X0_56,X1_56,X0_55,X2_56) = k7_relat_1(X0_55,X2_56)
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2399])).

cnf(c_3830,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_56) = k7_relat_1(sK4,X0_56)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3275,c_3245])).

cnf(c_5098,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_56) = k7_relat_1(sK4,X0_56) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3830,c_81])).

cnf(c_6443,plain,
    ( k2_tmap_1(sK2,sK3,sK4,X0_54) = k7_relat_1(sK4,u1_struct_0(X0_54))
    | m1_pre_topc(X0_54,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6438,c_5098])).

cnf(c_6450,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_6222,c_6443])).

cnf(c_16,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | sP0(X4,X3,X2,X1,X0)
    | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
    | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
    | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
    | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_26,plain,
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
    inference(cnf_transformation,[],[f76])).

cnf(c_60,negated_conjecture,
    ( r4_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_772,plain,
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
    inference(resolution_lifted,[status(thm)],[c_26,c_60])).

cnf(c_773,plain,
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
    inference(unflattening,[status(thm)],[c_772])).

cnf(c_777,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | sP1(sK5,sK2,X0,sK6,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_773,c_74,c_73,c_72,c_65,c_64,c_63,c_62])).

cnf(c_778,plain,
    ( sP1(sK5,sK2,X0,sK6,X1)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_777])).

cnf(c_813,plain,
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
    inference(resolution_lifted,[status(thm)],[c_16,c_778])).

cnf(c_814,plain,
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
    inference(unflattening,[status(thm)],[c_813])).

cnf(c_2357,plain,
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
    inference(subtyping,[status(esa)],[c_814])).

cnf(c_3286,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_2357])).

cnf(c_3295,plain,
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
    inference(light_normalisation,[status(thm)],[c_3286,c_2373])).

cnf(c_6935,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6450,c_3295])).

cnf(c_6938,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK2)),sK2,sK3) != iProver_top
    | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6935,c_6450])).

cnf(c_83,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66])).

cnf(c_12,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_942,plain,
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
    inference(resolution_lifted,[status(thm)],[c_12,c_778])).

cnf(c_943,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_942])).

cnf(c_2353,plain,
    ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
    | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54))))
    | v2_struct_0(X0_54)
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_943])).

cnf(c_3290,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54)))) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2353])).

cnf(c_3294,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3290,c_2373])).

cnf(c_6936,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6450,c_3294])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_178,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_180,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_2398,plain,
    ( ~ l1_pre_topc(X0_54)
    | l1_struct_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3678,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2398])).

cnf(c_3679,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3678])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2393,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | m1_subset_1(k2_tmap_1(X0_54,X1_54,X0_55,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | ~ l1_struct_0(X2_54)
    | ~ l1_struct_0(X1_54)
    | ~ l1_struct_0(X0_54)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_3251,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_54,X1_54,X0_55,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) = iProver_top
    | l1_struct_0(X2_54) != iProver_top
    | l1_struct_0(X1_54) != iProver_top
    | l1_struct_0(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2393])).

cnf(c_8535,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6450,c_3251])).

cnf(c_8929,plain,
    ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6936,c_77,c_80,c_81,c_82,c_83,c_180,c_3679,c_8535])).

cnf(c_13,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_912,plain,
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
    inference(resolution_lifted,[status(thm)],[c_13,c_778])).

cnf(c_913,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_912])).

cnf(c_2354,plain,
    ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_54)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
    | v2_struct_0(X0_54)
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_913])).

cnf(c_3289,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_54) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2354])).

cnf(c_3292,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3289,c_2373])).

cnf(c_8933,plain,
    ( sP0(sK3,sK6,k7_relat_1(sK4,u1_struct_0(sK2)),sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,k7_relat_1(sK4,u1_struct_0(sK2)),sK2),sK2,sK3) = iProver_top
    | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8929,c_3292])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2392,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | v1_funct_2(k2_tmap_1(X0_54,X1_54,X0_55,X2_54),u1_struct_0(X2_54),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ l1_struct_0(X2_54)
    | ~ l1_struct_0(X1_54)
    | ~ l1_struct_0(X0_54)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3252,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_54,X1_54,X0_55,X2_54),u1_struct_0(X2_54),u1_struct_0(X1_54)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | l1_struct_0(X2_54) != iProver_top
    | l1_struct_0(X1_54) != iProver_top
    | l1_struct_0(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2392])).

cnf(c_8666,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6450,c_3252])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2391,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ l1_struct_0(X2_54)
    | ~ l1_struct_0(X1_54)
    | ~ l1_struct_0(X0_54)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k2_tmap_1(X0_54,X1_54,X0_55,X2_54)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_3253,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | l1_struct_0(X2_54) != iProver_top
    | l1_struct_0(X1_54) != iProver_top
    | l1_struct_0(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_54,X1_54,X0_55,X2_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2391])).

cnf(c_8560,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | l1_struct_0(X0_54) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3275,c_3253])).

cnf(c_8784,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54)) = iProver_top
    | l1_struct_0(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8560,c_77,c_80,c_81,c_82,c_180,c_3679])).

cnf(c_8785,plain,
    ( l1_struct_0(X0_54) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8784])).

cnf(c_8792,plain,
    ( l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6450,c_8785])).

cnf(c_9102,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,k7_relat_1(sK4,u1_struct_0(sK2)),sK2),sK2,sK3) = iProver_top
    | sP0(sK3,sK6,k7_relat_1(sK4,u1_struct_0(sK2)),sK2,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8933,c_77,c_78,c_79,c_80,c_81,c_82,c_83,c_180,c_3679,c_8666,c_8792])).

cnf(c_9103,plain,
    ( sP0(sK3,sK6,k7_relat_1(sK4,u1_struct_0(sK2)),sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,k7_relat_1(sK4,u1_struct_0(sK2)),sK2),sK2,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_9102])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_0,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_752,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_2,c_0])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_756,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_752,c_2,c_1,c_0])).

cnf(c_2358,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | k7_relat_1(X0_55,X0_56) = X0_55 ),
    inference(subtyping,[status(esa)],[c_756])).

cnf(c_3285,plain,
    ( k7_relat_1(X0_55,X0_56) = X0_55
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2358])).

cnf(c_8985,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK4 ),
    inference(superposition,[status(thm)],[c_3275,c_3285])).

cnf(c_9035,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4 ),
    inference(demodulation,[status(thm)],[c_8985,c_6450])).

cnf(c_9106,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9103,c_8985,c_9035])).

cnf(c_53,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_95,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_49,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_99,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_45,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_103,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_37,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_111,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_33,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_115,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_29,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_119,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3394,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2391])).

cnf(c_3395,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3394])).

cnf(c_17,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2390,plain,
    ( sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
    | ~ v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),X1_54,X0_54)
    | ~ v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),X3_54,X0_54)
    | ~ v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),u1_struct_0(X1_54),u1_struct_0(X0_54))
    | ~ v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),u1_struct_0(X3_54),u1_struct_0(X0_54))
    | ~ m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54))))
    | ~ m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X0_54))))
    | ~ v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_55,X1_54))
    | ~ v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_55,X3_54)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_3466,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5)
    | ~ v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK5),sK5,X0_54)
    | ~ v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK6),sK6,X0_54)
    | ~ v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK5),u1_struct_0(sK5),u1_struct_0(X0_54))
    | ~ v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK6),u1_struct_0(sK6),u1_struct_0(X0_54))
    | ~ m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54))))
    | ~ m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_54))))
    | ~ v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK6)) ),
    inference(instantiation,[status(thm)],[c_2390])).

cnf(c_3467,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK5),sK5,X0_54) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK6),sK6,X0_54) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK5),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK6),u1_struct_0(sK6),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3466])).

cnf(c_3469,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3467])).

cnf(c_3502,plain,
    ( ~ l1_pre_topc(sK5)
    | l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2398])).

cnf(c_3503,plain,
    ( l1_pre_topc(sK5) != iProver_top
    | l1_struct_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3502])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2397,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3619,plain,
    ( ~ m1_pre_topc(sK5,X0_54)
    | ~ l1_pre_topc(X0_54)
    | l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_2397])).

cnf(c_3897,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3619])).

cnf(c_3898,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | l1_pre_topc(sK5) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3897])).

cnf(c_2372,negated_conjecture,
    ( m1_pre_topc(sK6,sK2) ),
    inference(subtyping,[status(esa)],[c_62])).

cnf(c_3271,plain,
    ( m1_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2372])).

cnf(c_3247,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2397])).

cnf(c_3968,plain,
    ( l1_pre_topc(sK6) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3271,c_3247])).

cnf(c_4978,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3968,c_77])).

cnf(c_3246,plain,
    ( l1_pre_topc(X0_54) != iProver_top
    | l1_struct_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2398])).

cnf(c_4982,plain,
    ( l1_struct_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4978,c_3246])).

cnf(c_5501,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(X0_54)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2391])).

cnf(c_6404,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK6)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5501])).

cnf(c_6405,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6404])).

cnf(c_9108,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9106,c_77,c_80,c_81,c_82,c_83,c_85,c_95,c_99,c_103,c_111,c_115,c_119,c_180,c_3395,c_3469,c_3503,c_3679,c_3898,c_4982,c_6405])).

cnf(c_8540,plain,
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
    inference(superposition,[status(thm)],[c_3251,c_3295])).

cnf(c_2447,plain,
    ( l1_pre_topc(X0_54) != iProver_top
    | l1_struct_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2398])).

cnf(c_9181,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_8540,c_77,c_2447,c_3679])).

cnf(c_10209,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9035,c_9181])).

cnf(c_10219,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10209,c_9035])).

cnf(c_11032,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6938,c_77,c_78,c_79,c_80,c_81,c_82,c_83,c_85,c_95,c_99,c_103,c_111,c_115,c_119,c_180,c_3395,c_3469,c_3503,c_3679,c_3898,c_4982,c_6405,c_9106,c_10219])).

cnf(c_23,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2384,plain,
    ( ~ sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
    | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),X3_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_3260,plain,
    ( sP0(X0_54,X1_54,X0_55,X2_54,X3_54) != iProver_top
    | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),X3_54,X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2384])).

cnf(c_11040,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_11032,c_3260])).

cnf(c_2370,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(subtyping,[status(esa)],[c_64])).

cnf(c_3273,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2370])).

cnf(c_6448,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK5) = k7_relat_1(sK4,u1_struct_0(sK5)) ),
    inference(superposition,[status(thm)],[c_3273,c_6443])).

cnf(c_11047,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11040,c_6448])).

cnf(c_19,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2388,plain,
    ( ~ sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
    | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),X1_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_3256,plain,
    ( sP0(X0_54,X1_54,X0_55,X2_54,X3_54) != iProver_top
    | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),X1_54,X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2388])).

cnf(c_11041,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_11032,c_3256])).

cnf(c_6447,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK6) = k7_relat_1(sK4,u1_struct_0(sK6)) ),
    inference(superposition,[status(thm)],[c_3271,c_6443])).

cnf(c_11046,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11041,c_6447])).

cnf(c_27,negated_conjecture,
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
    inference(cnf_transformation,[],[f124])).

cnf(c_484,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_68,c_67,c_66])).

cnf(c_485,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(renaming,[status(thm)],[c_484])).

cnf(c_2359,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(subtyping,[status(esa)],[c_485])).

cnf(c_3284,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2359])).

cnf(c_6459,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6447,c_3284])).

cnf(c_6460,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) != iProver_top
    | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK5))) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6459,c_6448])).

cnf(c_8533,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6447,c_3251])).

cnf(c_8534,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6448,c_3251])).

cnf(c_8664,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6447,c_3252])).

cnf(c_8665,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6448,c_3252])).

cnf(c_8790,plain,
    ( l1_struct_0(sK6) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6447,c_8785])).

cnf(c_8791,plain,
    ( l1_struct_0(sK5) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6448,c_8785])).

cnf(c_10312,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) != iProver_top
    | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6460,c_77,c_80,c_81,c_82,c_83,c_85,c_95,c_99,c_103,c_111,c_115,c_119,c_180,c_3395,c_3469,c_3503,c_3679,c_3898,c_4982,c_6405,c_8533,c_8534,c_8664,c_8665,c_8790,c_8791,c_9106])).

cnf(c_10313,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) != iProver_top
    | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_10312])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11047,c_11046,c_10313])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.08/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.02  
% 4.08/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.08/1.02  
% 4.08/1.02  ------  iProver source info
% 4.08/1.02  
% 4.08/1.02  git: date: 2020-06-30 10:37:57 +0100
% 4.08/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.08/1.02  git: non_committed_changes: false
% 4.08/1.02  git: last_make_outside_of_git: false
% 4.08/1.02  
% 4.08/1.02  ------ 
% 4.08/1.02  
% 4.08/1.02  ------ Input Options
% 4.08/1.02  
% 4.08/1.02  --out_options                           all
% 4.08/1.02  --tptp_safe_out                         true
% 4.08/1.02  --problem_path                          ""
% 4.08/1.02  --include_path                          ""
% 4.08/1.02  --clausifier                            res/vclausify_rel
% 4.08/1.02  --clausifier_options                    ""
% 4.08/1.02  --stdin                                 false
% 4.08/1.02  --stats_out                             all
% 4.08/1.02  
% 4.08/1.02  ------ General Options
% 4.08/1.02  
% 4.08/1.02  --fof                                   false
% 4.08/1.02  --time_out_real                         305.
% 4.08/1.02  --time_out_virtual                      -1.
% 4.08/1.02  --symbol_type_check                     false
% 4.08/1.02  --clausify_out                          false
% 4.08/1.02  --sig_cnt_out                           false
% 4.08/1.02  --trig_cnt_out                          false
% 4.08/1.02  --trig_cnt_out_tolerance                1.
% 4.08/1.02  --trig_cnt_out_sk_spl                   false
% 4.08/1.02  --abstr_cl_out                          false
% 4.08/1.02  
% 4.08/1.02  ------ Global Options
% 4.08/1.02  
% 4.08/1.02  --schedule                              default
% 4.08/1.02  --add_important_lit                     false
% 4.08/1.02  --prop_solver_per_cl                    1000
% 4.08/1.02  --min_unsat_core                        false
% 4.08/1.02  --soft_assumptions                      false
% 4.08/1.02  --soft_lemma_size                       3
% 4.08/1.02  --prop_impl_unit_size                   0
% 4.08/1.02  --prop_impl_unit                        []
% 4.08/1.02  --share_sel_clauses                     true
% 4.08/1.02  --reset_solvers                         false
% 4.08/1.02  --bc_imp_inh                            [conj_cone]
% 4.08/1.02  --conj_cone_tolerance                   3.
% 4.08/1.02  --extra_neg_conj                        none
% 4.08/1.02  --large_theory_mode                     true
% 4.08/1.02  --prolific_symb_bound                   200
% 4.08/1.02  --lt_threshold                          2000
% 4.08/1.02  --clause_weak_htbl                      true
% 4.08/1.02  --gc_record_bc_elim                     false
% 4.08/1.02  
% 4.08/1.02  ------ Preprocessing Options
% 4.08/1.02  
% 4.08/1.02  --preprocessing_flag                    true
% 4.08/1.02  --time_out_prep_mult                    0.1
% 4.08/1.02  --splitting_mode                        input
% 4.08/1.02  --splitting_grd                         true
% 4.08/1.02  --splitting_cvd                         false
% 4.08/1.02  --splitting_cvd_svl                     false
% 4.08/1.02  --splitting_nvd                         32
% 4.08/1.02  --sub_typing                            true
% 4.08/1.02  --prep_gs_sim                           true
% 4.08/1.02  --prep_unflatten                        true
% 4.08/1.02  --prep_res_sim                          true
% 4.08/1.02  --prep_upred                            true
% 4.08/1.02  --prep_sem_filter                       exhaustive
% 4.08/1.02  --prep_sem_filter_out                   false
% 4.08/1.02  --pred_elim                             true
% 4.08/1.02  --res_sim_input                         true
% 4.08/1.02  --eq_ax_congr_red                       true
% 4.08/1.02  --pure_diseq_elim                       true
% 4.08/1.02  --brand_transform                       false
% 4.08/1.02  --non_eq_to_eq                          false
% 4.08/1.02  --prep_def_merge                        true
% 4.08/1.02  --prep_def_merge_prop_impl              false
% 4.08/1.02  --prep_def_merge_mbd                    true
% 4.08/1.02  --prep_def_merge_tr_red                 false
% 4.08/1.02  --prep_def_merge_tr_cl                  false
% 4.08/1.02  --smt_preprocessing                     true
% 4.08/1.02  --smt_ac_axioms                         fast
% 4.08/1.02  --preprocessed_out                      false
% 4.08/1.02  --preprocessed_stats                    false
% 4.08/1.02  
% 4.08/1.02  ------ Abstraction refinement Options
% 4.08/1.02  
% 4.08/1.02  --abstr_ref                             []
% 4.08/1.02  --abstr_ref_prep                        false
% 4.08/1.02  --abstr_ref_until_sat                   false
% 4.08/1.02  --abstr_ref_sig_restrict                funpre
% 4.08/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 4.08/1.02  --abstr_ref_under                       []
% 4.08/1.02  
% 4.08/1.02  ------ SAT Options
% 4.08/1.02  
% 4.08/1.02  --sat_mode                              false
% 4.08/1.02  --sat_fm_restart_options                ""
% 4.08/1.02  --sat_gr_def                            false
% 4.08/1.02  --sat_epr_types                         true
% 4.08/1.02  --sat_non_cyclic_types                  false
% 4.08/1.02  --sat_finite_models                     false
% 4.08/1.02  --sat_fm_lemmas                         false
% 4.08/1.02  --sat_fm_prep                           false
% 4.08/1.02  --sat_fm_uc_incr                        true
% 4.08/1.02  --sat_out_model                         small
% 4.08/1.02  --sat_out_clauses                       false
% 4.08/1.02  
% 4.08/1.02  ------ QBF Options
% 4.08/1.02  
% 4.08/1.02  --qbf_mode                              false
% 4.08/1.02  --qbf_elim_univ                         false
% 4.08/1.02  --qbf_dom_inst                          none
% 4.08/1.02  --qbf_dom_pre_inst                      false
% 4.08/1.02  --qbf_sk_in                             false
% 4.08/1.02  --qbf_pred_elim                         true
% 4.08/1.02  --qbf_split                             512
% 4.08/1.02  
% 4.08/1.02  ------ BMC1 Options
% 4.08/1.02  
% 4.08/1.02  --bmc1_incremental                      false
% 4.08/1.02  --bmc1_axioms                           reachable_all
% 4.08/1.02  --bmc1_min_bound                        0
% 4.08/1.02  --bmc1_max_bound                        -1
% 4.08/1.02  --bmc1_max_bound_default                -1
% 4.08/1.02  --bmc1_symbol_reachability              true
% 4.08/1.02  --bmc1_property_lemmas                  false
% 4.08/1.02  --bmc1_k_induction                      false
% 4.08/1.02  --bmc1_non_equiv_states                 false
% 4.08/1.02  --bmc1_deadlock                         false
% 4.08/1.02  --bmc1_ucm                              false
% 4.08/1.02  --bmc1_add_unsat_core                   none
% 4.08/1.02  --bmc1_unsat_core_children              false
% 4.08/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 4.08/1.02  --bmc1_out_stat                         full
% 4.08/1.02  --bmc1_ground_init                      false
% 4.08/1.02  --bmc1_pre_inst_next_state              false
% 4.08/1.02  --bmc1_pre_inst_state                   false
% 4.08/1.02  --bmc1_pre_inst_reach_state             false
% 4.08/1.02  --bmc1_out_unsat_core                   false
% 4.08/1.02  --bmc1_aig_witness_out                  false
% 4.08/1.02  --bmc1_verbose                          false
% 4.08/1.02  --bmc1_dump_clauses_tptp                false
% 4.08/1.02  --bmc1_dump_unsat_core_tptp             false
% 4.08/1.02  --bmc1_dump_file                        -
% 4.08/1.02  --bmc1_ucm_expand_uc_limit              128
% 4.08/1.02  --bmc1_ucm_n_expand_iterations          6
% 4.08/1.02  --bmc1_ucm_extend_mode                  1
% 4.08/1.02  --bmc1_ucm_init_mode                    2
% 4.08/1.02  --bmc1_ucm_cone_mode                    none
% 4.08/1.02  --bmc1_ucm_reduced_relation_type        0
% 4.08/1.02  --bmc1_ucm_relax_model                  4
% 4.08/1.02  --bmc1_ucm_full_tr_after_sat            true
% 4.08/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 4.08/1.02  --bmc1_ucm_layered_model                none
% 4.08/1.02  --bmc1_ucm_max_lemma_size               10
% 4.08/1.02  
% 4.08/1.02  ------ AIG Options
% 4.08/1.02  
% 4.08/1.02  --aig_mode                              false
% 4.08/1.02  
% 4.08/1.02  ------ Instantiation Options
% 4.08/1.02  
% 4.08/1.02  --instantiation_flag                    true
% 4.08/1.02  --inst_sos_flag                         true
% 4.08/1.02  --inst_sos_phase                        true
% 4.08/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.08/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.08/1.02  --inst_lit_sel_side                     num_symb
% 4.08/1.02  --inst_solver_per_active                1400
% 4.08/1.02  --inst_solver_calls_frac                1.
% 4.08/1.02  --inst_passive_queue_type               priority_queues
% 4.08/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.08/1.02  --inst_passive_queues_freq              [25;2]
% 4.08/1.02  --inst_dismatching                      true
% 4.08/1.02  --inst_eager_unprocessed_to_passive     true
% 4.08/1.02  --inst_prop_sim_given                   true
% 4.08/1.02  --inst_prop_sim_new                     false
% 4.08/1.02  --inst_subs_new                         false
% 4.08/1.02  --inst_eq_res_simp                      false
% 4.08/1.02  --inst_subs_given                       false
% 4.08/1.02  --inst_orphan_elimination               true
% 4.08/1.02  --inst_learning_loop_flag               true
% 4.08/1.02  --inst_learning_start                   3000
% 4.08/1.02  --inst_learning_factor                  2
% 4.08/1.02  --inst_start_prop_sim_after_learn       3
% 4.08/1.02  --inst_sel_renew                        solver
% 4.08/1.02  --inst_lit_activity_flag                true
% 4.08/1.02  --inst_restr_to_given                   false
% 4.08/1.02  --inst_activity_threshold               500
% 4.08/1.02  --inst_out_proof                        true
% 4.08/1.02  
% 4.08/1.02  ------ Resolution Options
% 4.08/1.02  
% 4.08/1.02  --resolution_flag                       true
% 4.08/1.02  --res_lit_sel                           adaptive
% 4.08/1.02  --res_lit_sel_side                      none
% 4.08/1.02  --res_ordering                          kbo
% 4.08/1.02  --res_to_prop_solver                    active
% 4.08/1.02  --res_prop_simpl_new                    false
% 4.08/1.02  --res_prop_simpl_given                  true
% 4.08/1.02  --res_passive_queue_type                priority_queues
% 4.08/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.08/1.02  --res_passive_queues_freq               [15;5]
% 4.08/1.02  --res_forward_subs                      full
% 4.08/1.02  --res_backward_subs                     full
% 4.08/1.02  --res_forward_subs_resolution           true
% 4.08/1.02  --res_backward_subs_resolution          true
% 4.08/1.02  --res_orphan_elimination                true
% 4.08/1.02  --res_time_limit                        2.
% 4.08/1.02  --res_out_proof                         true
% 4.08/1.02  
% 4.08/1.02  ------ Superposition Options
% 4.08/1.02  
% 4.08/1.02  --superposition_flag                    true
% 4.08/1.02  --sup_passive_queue_type                priority_queues
% 4.08/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.08/1.02  --sup_passive_queues_freq               [8;1;4]
% 4.08/1.02  --demod_completeness_check              fast
% 4.08/1.02  --demod_use_ground                      true
% 4.08/1.02  --sup_to_prop_solver                    passive
% 4.08/1.02  --sup_prop_simpl_new                    true
% 4.08/1.02  --sup_prop_simpl_given                  true
% 4.08/1.02  --sup_fun_splitting                     true
% 4.08/1.02  --sup_smt_interval                      50000
% 4.08/1.02  
% 4.08/1.02  ------ Superposition Simplification Setup
% 4.08/1.02  
% 4.08/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.08/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.08/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.08/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.08/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 4.08/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.08/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.08/1.02  --sup_immed_triv                        [TrivRules]
% 4.08/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.08/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.08/1.02  --sup_immed_bw_main                     []
% 4.08/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.08/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 4.08/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.08/1.02  --sup_input_bw                          []
% 4.08/1.02  
% 4.08/1.02  ------ Combination Options
% 4.08/1.02  
% 4.08/1.02  --comb_res_mult                         3
% 4.08/1.02  --comb_sup_mult                         2
% 4.08/1.02  --comb_inst_mult                        10
% 4.08/1.02  
% 4.08/1.02  ------ Debug Options
% 4.08/1.02  
% 4.08/1.02  --dbg_backtrace                         false
% 4.08/1.02  --dbg_dump_prop_clauses                 false
% 4.08/1.02  --dbg_dump_prop_clauses_file            -
% 4.08/1.02  --dbg_out_stat                          false
% 4.08/1.02  ------ Parsing...
% 4.08/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.08/1.02  
% 4.08/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.08/1.02  
% 4.08/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.08/1.02  
% 4.08/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.08/1.02  ------ Proving...
% 4.08/1.02  ------ Problem Properties 
% 4.08/1.02  
% 4.08/1.02  
% 4.08/1.02  clauses                                 47
% 4.08/1.02  conjectures                             23
% 4.08/1.02  EPR                                     13
% 4.08/1.02  Horn                                    31
% 4.08/1.02  unary                                   14
% 4.08/1.02  binary                                  18
% 4.08/1.02  lits                                    163
% 4.08/1.02  lits eq                                 4
% 4.08/1.02  fd_pure                                 0
% 4.08/1.02  fd_pseudo                               0
% 4.08/1.02  fd_cond                                 0
% 4.08/1.02  fd_pseudo_cond                          0
% 4.08/1.02  AC symbols                              0
% 4.08/1.02  
% 4.08/1.02  ------ Schedule dynamic 5 is on 
% 4.08/1.02  
% 4.08/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.08/1.02  
% 4.08/1.02  
% 4.08/1.02  ------ 
% 4.08/1.02  Current options:
% 4.08/1.02  ------ 
% 4.08/1.02  
% 4.08/1.02  ------ Input Options
% 4.08/1.02  
% 4.08/1.02  --out_options                           all
% 4.08/1.02  --tptp_safe_out                         true
% 4.08/1.02  --problem_path                          ""
% 4.08/1.02  --include_path                          ""
% 4.08/1.02  --clausifier                            res/vclausify_rel
% 4.08/1.02  --clausifier_options                    ""
% 4.08/1.02  --stdin                                 false
% 4.08/1.02  --stats_out                             all
% 4.08/1.02  
% 4.08/1.02  ------ General Options
% 4.08/1.02  
% 4.08/1.02  --fof                                   false
% 4.08/1.02  --time_out_real                         305.
% 4.08/1.02  --time_out_virtual                      -1.
% 4.08/1.02  --symbol_type_check                     false
% 4.08/1.02  --clausify_out                          false
% 4.08/1.02  --sig_cnt_out                           false
% 4.08/1.02  --trig_cnt_out                          false
% 4.08/1.02  --trig_cnt_out_tolerance                1.
% 4.08/1.02  --trig_cnt_out_sk_spl                   false
% 4.08/1.02  --abstr_cl_out                          false
% 4.08/1.02  
% 4.08/1.02  ------ Global Options
% 4.08/1.02  
% 4.08/1.02  --schedule                              default
% 4.08/1.02  --add_important_lit                     false
% 4.08/1.02  --prop_solver_per_cl                    1000
% 4.08/1.02  --min_unsat_core                        false
% 4.08/1.02  --soft_assumptions                      false
% 4.08/1.02  --soft_lemma_size                       3
% 4.08/1.02  --prop_impl_unit_size                   0
% 4.08/1.02  --prop_impl_unit                        []
% 4.08/1.02  --share_sel_clauses                     true
% 4.08/1.02  --reset_solvers                         false
% 4.08/1.02  --bc_imp_inh                            [conj_cone]
% 4.08/1.02  --conj_cone_tolerance                   3.
% 4.08/1.02  --extra_neg_conj                        none
% 4.08/1.02  --large_theory_mode                     true
% 4.08/1.02  --prolific_symb_bound                   200
% 4.08/1.02  --lt_threshold                          2000
% 4.08/1.02  --clause_weak_htbl                      true
% 4.08/1.02  --gc_record_bc_elim                     false
% 4.08/1.02  
% 4.08/1.02  ------ Preprocessing Options
% 4.08/1.02  
% 4.08/1.02  --preprocessing_flag                    true
% 4.08/1.02  --time_out_prep_mult                    0.1
% 4.08/1.02  --splitting_mode                        input
% 4.08/1.02  --splitting_grd                         true
% 4.08/1.02  --splitting_cvd                         false
% 4.08/1.02  --splitting_cvd_svl                     false
% 4.08/1.02  --splitting_nvd                         32
% 4.08/1.02  --sub_typing                            true
% 4.08/1.02  --prep_gs_sim                           true
% 4.08/1.02  --prep_unflatten                        true
% 4.08/1.02  --prep_res_sim                          true
% 4.08/1.02  --prep_upred                            true
% 4.08/1.02  --prep_sem_filter                       exhaustive
% 4.08/1.02  --prep_sem_filter_out                   false
% 4.08/1.02  --pred_elim                             true
% 4.08/1.02  --res_sim_input                         true
% 4.08/1.02  --eq_ax_congr_red                       true
% 4.08/1.02  --pure_diseq_elim                       true
% 4.08/1.02  --brand_transform                       false
% 4.08/1.02  --non_eq_to_eq                          false
% 4.08/1.02  --prep_def_merge                        true
% 4.08/1.02  --prep_def_merge_prop_impl              false
% 4.08/1.02  --prep_def_merge_mbd                    true
% 4.08/1.02  --prep_def_merge_tr_red                 false
% 4.08/1.02  --prep_def_merge_tr_cl                  false
% 4.08/1.02  --smt_preprocessing                     true
% 4.08/1.02  --smt_ac_axioms                         fast
% 4.08/1.02  --preprocessed_out                      false
% 4.08/1.02  --preprocessed_stats                    false
% 4.08/1.02  
% 4.08/1.02  ------ Abstraction refinement Options
% 4.08/1.02  
% 4.08/1.02  --abstr_ref                             []
% 4.08/1.02  --abstr_ref_prep                        false
% 4.08/1.02  --abstr_ref_until_sat                   false
% 4.08/1.02  --abstr_ref_sig_restrict                funpre
% 4.08/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 4.08/1.02  --abstr_ref_under                       []
% 4.08/1.02  
% 4.08/1.02  ------ SAT Options
% 4.08/1.02  
% 4.08/1.02  --sat_mode                              false
% 4.08/1.02  --sat_fm_restart_options                ""
% 4.08/1.02  --sat_gr_def                            false
% 4.08/1.02  --sat_epr_types                         true
% 4.08/1.02  --sat_non_cyclic_types                  false
% 4.08/1.02  --sat_finite_models                     false
% 4.08/1.02  --sat_fm_lemmas                         false
% 4.08/1.02  --sat_fm_prep                           false
% 4.08/1.02  --sat_fm_uc_incr                        true
% 4.08/1.02  --sat_out_model                         small
% 4.08/1.02  --sat_out_clauses                       false
% 4.08/1.02  
% 4.08/1.02  ------ QBF Options
% 4.08/1.02  
% 4.08/1.02  --qbf_mode                              false
% 4.08/1.02  --qbf_elim_univ                         false
% 4.08/1.02  --qbf_dom_inst                          none
% 4.08/1.02  --qbf_dom_pre_inst                      false
% 4.08/1.02  --qbf_sk_in                             false
% 4.08/1.02  --qbf_pred_elim                         true
% 4.08/1.02  --qbf_split                             512
% 4.08/1.02  
% 4.08/1.02  ------ BMC1 Options
% 4.08/1.02  
% 4.08/1.02  --bmc1_incremental                      false
% 4.08/1.02  --bmc1_axioms                           reachable_all
% 4.08/1.02  --bmc1_min_bound                        0
% 4.08/1.02  --bmc1_max_bound                        -1
% 4.08/1.02  --bmc1_max_bound_default                -1
% 4.08/1.02  --bmc1_symbol_reachability              true
% 4.08/1.02  --bmc1_property_lemmas                  false
% 4.08/1.02  --bmc1_k_induction                      false
% 4.08/1.02  --bmc1_non_equiv_states                 false
% 4.08/1.02  --bmc1_deadlock                         false
% 4.08/1.02  --bmc1_ucm                              false
% 4.08/1.02  --bmc1_add_unsat_core                   none
% 4.08/1.02  --bmc1_unsat_core_children              false
% 4.08/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 4.08/1.02  --bmc1_out_stat                         full
% 4.08/1.02  --bmc1_ground_init                      false
% 4.08/1.02  --bmc1_pre_inst_next_state              false
% 4.08/1.02  --bmc1_pre_inst_state                   false
% 4.08/1.02  --bmc1_pre_inst_reach_state             false
% 4.08/1.02  --bmc1_out_unsat_core                   false
% 4.08/1.02  --bmc1_aig_witness_out                  false
% 4.08/1.02  --bmc1_verbose                          false
% 4.08/1.02  --bmc1_dump_clauses_tptp                false
% 4.08/1.02  --bmc1_dump_unsat_core_tptp             false
% 4.08/1.02  --bmc1_dump_file                        -
% 4.08/1.02  --bmc1_ucm_expand_uc_limit              128
% 4.08/1.02  --bmc1_ucm_n_expand_iterations          6
% 4.08/1.02  --bmc1_ucm_extend_mode                  1
% 4.08/1.02  --bmc1_ucm_init_mode                    2
% 4.08/1.02  --bmc1_ucm_cone_mode                    none
% 4.08/1.02  --bmc1_ucm_reduced_relation_type        0
% 4.08/1.02  --bmc1_ucm_relax_model                  4
% 4.08/1.02  --bmc1_ucm_full_tr_after_sat            true
% 4.08/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 4.08/1.02  --bmc1_ucm_layered_model                none
% 4.08/1.02  --bmc1_ucm_max_lemma_size               10
% 4.08/1.02  
% 4.08/1.02  ------ AIG Options
% 4.08/1.02  
% 4.08/1.02  --aig_mode                              false
% 4.08/1.02  
% 4.08/1.02  ------ Instantiation Options
% 4.08/1.02  
% 4.08/1.02  --instantiation_flag                    true
% 4.08/1.02  --inst_sos_flag                         true
% 4.08/1.02  --inst_sos_phase                        true
% 4.08/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.08/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.08/1.02  --inst_lit_sel_side                     none
% 4.08/1.02  --inst_solver_per_active                1400
% 4.08/1.02  --inst_solver_calls_frac                1.
% 4.08/1.02  --inst_passive_queue_type               priority_queues
% 4.08/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.08/1.02  --inst_passive_queues_freq              [25;2]
% 4.08/1.02  --inst_dismatching                      true
% 4.08/1.02  --inst_eager_unprocessed_to_passive     true
% 4.08/1.02  --inst_prop_sim_given                   true
% 4.08/1.02  --inst_prop_sim_new                     false
% 4.08/1.02  --inst_subs_new                         false
% 4.08/1.02  --inst_eq_res_simp                      false
% 4.08/1.02  --inst_subs_given                       false
% 4.08/1.02  --inst_orphan_elimination               true
% 4.08/1.02  --inst_learning_loop_flag               true
% 4.08/1.02  --inst_learning_start                   3000
% 4.08/1.02  --inst_learning_factor                  2
% 4.08/1.02  --inst_start_prop_sim_after_learn       3
% 4.08/1.02  --inst_sel_renew                        solver
% 4.08/1.02  --inst_lit_activity_flag                true
% 4.08/1.02  --inst_restr_to_given                   false
% 4.08/1.02  --inst_activity_threshold               500
% 4.08/1.02  --inst_out_proof                        true
% 4.08/1.02  
% 4.08/1.02  ------ Resolution Options
% 4.08/1.02  
% 4.08/1.02  --resolution_flag                       false
% 4.08/1.02  --res_lit_sel                           adaptive
% 4.08/1.02  --res_lit_sel_side                      none
% 4.08/1.02  --res_ordering                          kbo
% 4.08/1.02  --res_to_prop_solver                    active
% 4.08/1.02  --res_prop_simpl_new                    false
% 4.08/1.02  --res_prop_simpl_given                  true
% 4.08/1.02  --res_passive_queue_type                priority_queues
% 4.08/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.08/1.02  --res_passive_queues_freq               [15;5]
% 4.08/1.02  --res_forward_subs                      full
% 4.08/1.02  --res_backward_subs                     full
% 4.08/1.02  --res_forward_subs_resolution           true
% 4.08/1.02  --res_backward_subs_resolution          true
% 4.08/1.02  --res_orphan_elimination                true
% 4.08/1.02  --res_time_limit                        2.
% 4.08/1.02  --res_out_proof                         true
% 4.08/1.02  
% 4.08/1.02  ------ Superposition Options
% 4.08/1.02  
% 4.08/1.02  --superposition_flag                    true
% 4.08/1.02  --sup_passive_queue_type                priority_queues
% 4.08/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.08/1.02  --sup_passive_queues_freq               [8;1;4]
% 4.08/1.02  --demod_completeness_check              fast
% 4.08/1.02  --demod_use_ground                      true
% 4.08/1.02  --sup_to_prop_solver                    passive
% 4.08/1.02  --sup_prop_simpl_new                    true
% 4.08/1.02  --sup_prop_simpl_given                  true
% 4.08/1.02  --sup_fun_splitting                     true
% 4.08/1.02  --sup_smt_interval                      50000
% 4.08/1.02  
% 4.08/1.02  ------ Superposition Simplification Setup
% 4.08/1.02  
% 4.08/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.08/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.08/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.08/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.08/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 4.08/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.08/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.08/1.02  --sup_immed_triv                        [TrivRules]
% 4.08/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.08/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.08/1.02  --sup_immed_bw_main                     []
% 4.08/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.08/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 4.08/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.08/1.02  --sup_input_bw                          []
% 4.08/1.02  
% 4.08/1.02  ------ Combination Options
% 4.08/1.02  
% 4.08/1.02  --comb_res_mult                         3
% 4.08/1.02  --comb_sup_mult                         2
% 4.08/1.02  --comb_inst_mult                        10
% 4.08/1.02  
% 4.08/1.02  ------ Debug Options
% 4.08/1.02  
% 4.08/1.02  --dbg_backtrace                         false
% 4.08/1.02  --dbg_dump_prop_clauses                 false
% 4.08/1.02  --dbg_dump_prop_clauses_file            -
% 4.08/1.02  --dbg_out_stat                          false
% 4.08/1.02  
% 4.08/1.02  
% 4.08/1.02  
% 4.08/1.02  
% 4.08/1.02  ------ Proving...
% 4.08/1.02  
% 4.08/1.02  
% 4.08/1.02  % SZS status Theorem for theBenchmark.p
% 4.08/1.02  
% 4.08/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 4.08/1.02  
% 4.08/1.02  fof(f11,conjecture,(
% 4.08/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 4.08/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.02  
% 4.08/1.02  fof(f12,negated_conjecture,(
% 4.08/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 4.08/1.02    inference(negated_conjecture,[],[f11])).
% 4.08/1.02  
% 4.08/1.02  fof(f31,plain,(
% 4.08/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & (r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0)) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 4.08/1.02    inference(ennf_transformation,[],[f12])).
% 4.08/1.02  
% 4.08/1.02  fof(f32,plain,(
% 4.08/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.08/1.02    inference(flattening,[],[f31])).
% 4.08/1.02  
% 4.08/1.02  fof(f42,plain,(
% 4.08/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.08/1.02    inference(nnf_transformation,[],[f32])).
% 4.08/1.02  
% 4.08/1.02  fof(f43,plain,(
% 4.08/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.08/1.02    inference(flattening,[],[f42])).
% 4.08/1.02  
% 4.08/1.02  fof(f48,plain,(
% 4.08/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((~m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,sK6) & k1_tsep_1(X0,X3,sK6) = X0 & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 4.08/1.02    introduced(choice_axiom,[])).
% 4.08/1.02  
% 4.08/1.02  fof(f47,plain,(
% 4.08/1.02    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK5)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK5))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,sK5,X4) & k1_tsep_1(X0,sK5,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 4.08/1.02    introduced(choice_axiom,[])).
% 4.08/1.02  
% 4.08/1.02  fof(f46,plain,(
% 4.08/1.02    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(sK4,X0,X1) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) & m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X3))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK4,X0,X1) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 4.08/1.02    introduced(choice_axiom,[])).
% 4.08/1.02  
% 4.08/1.02  fof(f45,plain,(
% 4.08/1.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(X2,X0,sK3) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) & m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v5_pre_topc(X2,X0,sK3) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 4.08/1.02    introduced(choice_axiom,[])).
% 4.08/1.02  
% 4.08/1.02  fof(f44,plain,(
% 4.08/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(sK2,X3,X4) & k1_tsep_1(sK2,X3,X4) = sK2 & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 4.08/1.02    introduced(choice_axiom,[])).
% 4.08/1.02  
% 4.08/1.02  fof(f49,plain,(
% 4.08/1.02    (((((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,sK5,sK6) & k1_tsep_1(sK2,sK5,sK6) = sK2 & m1_pre_topc(sK6,sK2) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 4.08/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f43,f48,f47,f46,f45,f44])).
% 4.08/1.02  
% 4.08/1.02  fof(f90,plain,(
% 4.08/1.02    k1_tsep_1(sK2,sK5,sK6) = sK2),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  fof(f8,axiom,(
% 4.08/1.02    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 4.08/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.02  
% 4.08/1.02  fof(f13,plain,(
% 4.08/1.02    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 4.08/1.02    inference(pure_predicate_removal,[],[f8])).
% 4.08/1.02  
% 4.08/1.02  fof(f25,plain,(
% 4.08/1.02    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 4.08/1.02    inference(ennf_transformation,[],[f13])).
% 4.08/1.02  
% 4.08/1.02  fof(f26,plain,(
% 4.08/1.02    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 4.08/1.02    inference(flattening,[],[f25])).
% 4.08/1.02  
% 4.08/1.02  fof(f58,plain,(
% 4.08/1.02    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/1.02    inference(cnf_transformation,[],[f26])).
% 4.08/1.02  
% 4.08/1.02  fof(f77,plain,(
% 4.08/1.02    ~v2_struct_0(sK2)),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  fof(f79,plain,(
% 4.08/1.02    l1_pre_topc(sK2)),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  fof(f86,plain,(
% 4.08/1.02    ~v2_struct_0(sK5)),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  fof(f87,plain,(
% 4.08/1.02    m1_pre_topc(sK5,sK2)),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  fof(f88,plain,(
% 4.08/1.02    ~v2_struct_0(sK6)),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  fof(f89,plain,(
% 4.08/1.02    m1_pre_topc(sK6,sK2)),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  fof(f85,plain,(
% 4.08/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  fof(f7,axiom,(
% 4.08/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 4.08/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.02  
% 4.08/1.02  fof(f23,plain,(
% 4.08/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.08/1.02    inference(ennf_transformation,[],[f7])).
% 4.08/1.02  
% 4.08/1.02  fof(f24,plain,(
% 4.08/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.08/1.02    inference(flattening,[],[f23])).
% 4.08/1.02  
% 4.08/1.02  fof(f56,plain,(
% 4.08/1.02    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/1.02    inference(cnf_transformation,[],[f24])).
% 4.08/1.02  
% 4.08/1.02  fof(f78,plain,(
% 4.08/1.02    v2_pre_topc(sK2)),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  fof(f80,plain,(
% 4.08/1.02    ~v2_struct_0(sK3)),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  fof(f81,plain,(
% 4.08/1.02    v2_pre_topc(sK3)),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  fof(f82,plain,(
% 4.08/1.02    l1_pre_topc(sK3)),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  fof(f83,plain,(
% 4.08/1.02    v1_funct_1(sK4)),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  fof(f84,plain,(
% 4.08/1.02    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  fof(f4,axiom,(
% 4.08/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 4.08/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.02  
% 4.08/1.02  fof(f19,plain,(
% 4.08/1.02    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 4.08/1.02    inference(ennf_transformation,[],[f4])).
% 4.08/1.02  
% 4.08/1.02  fof(f20,plain,(
% 4.08/1.02    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 4.08/1.02    inference(flattening,[],[f19])).
% 4.08/1.02  
% 4.08/1.02  fof(f53,plain,(
% 4.08/1.02    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 4.08/1.02    inference(cnf_transformation,[],[f20])).
% 4.08/1.02  
% 4.08/1.02  fof(f34,plain,(
% 4.08/1.02    ! [X2,X0,X4,X3,X1] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> sP0(X1,X3,X4,X0,X2)) | ~sP1(X2,X0,X4,X3,X1))),
% 4.08/1.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 4.08/1.02  
% 4.08/1.02  fof(f36,plain,(
% 4.08/1.02    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))))) | ~sP1(X2,X0,X4,X3,X1))),
% 4.08/1.02    inference(nnf_transformation,[],[f34])).
% 4.08/1.02  
% 4.08/1.02  fof(f37,plain,(
% 4.08/1.02    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))))) | ~sP1(X2,X0,X4,X3,X1))),
% 4.08/1.02    inference(flattening,[],[f36])).
% 4.08/1.02  
% 4.08/1.02  fof(f38,plain,(
% 4.08/1.02    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) & v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) & v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) & v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))))) | ~sP1(X0,X1,X2,X3,X4))),
% 4.08/1.02    inference(rectify,[],[f37])).
% 4.08/1.02  
% 4.08/1.02  fof(f62,plain,(
% 4.08/1.02    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) | ~sP1(X0,X1,X2,X3,X4)) )),
% 4.08/1.02    inference(cnf_transformation,[],[f38])).
% 4.08/1.02  
% 4.08/1.02  fof(f10,axiom,(
% 4.08/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))))))))),
% 4.08/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.02  
% 4.08/1.02  fof(f29,plain,(
% 4.08/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.08/1.02    inference(ennf_transformation,[],[f10])).
% 4.08/1.02  
% 4.08/1.02  fof(f30,plain,(
% 4.08/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.08/1.02    inference(flattening,[],[f29])).
% 4.08/1.02  
% 4.08/1.02  fof(f33,plain,(
% 4.08/1.02    ! [X1,X3,X4,X0,X2] : (sP0(X1,X3,X4,X0,X2) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))),
% 4.08/1.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 4.08/1.02  
% 4.08/1.02  fof(f35,plain,(
% 4.08/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X2,X0,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.08/1.02    inference(definition_folding,[],[f30,f34,f33])).
% 4.08/1.02  
% 4.08/1.02  fof(f76,plain,(
% 4.08/1.02    ( ! [X4,X2,X0,X3,X1] : (sP1(X2,X0,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/1.02    inference(cnf_transformation,[],[f35])).
% 4.08/1.02  
% 4.08/1.02  fof(f91,plain,(
% 4.08/1.02    r4_tsep_1(sK2,sK5,sK6)),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  fof(f66,plain,(
% 4.08/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 4.08/1.02    inference(cnf_transformation,[],[f38])).
% 4.08/1.02  
% 4.08/1.02  fof(f5,axiom,(
% 4.08/1.02    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 4.08/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.02  
% 4.08/1.02  fof(f21,plain,(
% 4.08/1.02    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 4.08/1.02    inference(ennf_transformation,[],[f5])).
% 4.08/1.02  
% 4.08/1.02  fof(f54,plain,(
% 4.08/1.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 4.08/1.02    inference(cnf_transformation,[],[f21])).
% 4.08/1.02  
% 4.08/1.02  fof(f9,axiom,(
% 4.08/1.02    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 4.08/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.02  
% 4.08/1.02  fof(f27,plain,(
% 4.08/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 4.08/1.02    inference(ennf_transformation,[],[f9])).
% 4.08/1.02  
% 4.08/1.02  fof(f28,plain,(
% 4.08/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 4.08/1.02    inference(flattening,[],[f27])).
% 4.08/1.02  
% 4.08/1.02  fof(f61,plain,(
% 4.08/1.02    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 4.08/1.02    inference(cnf_transformation,[],[f28])).
% 4.08/1.02  
% 4.08/1.02  fof(f65,plain,(
% 4.08/1.02    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 4.08/1.02    inference(cnf_transformation,[],[f38])).
% 4.08/1.02  
% 4.08/1.02  fof(f60,plain,(
% 4.08/1.02    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 4.08/1.02    inference(cnf_transformation,[],[f28])).
% 4.08/1.02  
% 4.08/1.02  fof(f59,plain,(
% 4.08/1.02    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 4.08/1.02    inference(cnf_transformation,[],[f28])).
% 4.08/1.02  
% 4.08/1.02  fof(f3,axiom,(
% 4.08/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.08/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.02  
% 4.08/1.02  fof(f14,plain,(
% 4.08/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 4.08/1.02    inference(pure_predicate_removal,[],[f3])).
% 4.08/1.02  
% 4.08/1.02  fof(f18,plain,(
% 4.08/1.02    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.08/1.02    inference(ennf_transformation,[],[f14])).
% 4.08/1.02  
% 4.08/1.02  fof(f52,plain,(
% 4.08/1.02    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.08/1.02    inference(cnf_transformation,[],[f18])).
% 4.08/1.02  
% 4.08/1.02  fof(f1,axiom,(
% 4.08/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 4.08/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.02  
% 4.08/1.02  fof(f15,plain,(
% 4.08/1.02    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 4.08/1.02    inference(ennf_transformation,[],[f1])).
% 4.08/1.02  
% 4.08/1.02  fof(f16,plain,(
% 4.08/1.02    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.08/1.02    inference(flattening,[],[f15])).
% 4.08/1.02  
% 4.08/1.02  fof(f50,plain,(
% 4.08/1.02    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.08/1.02    inference(cnf_transformation,[],[f16])).
% 4.08/1.02  
% 4.08/1.02  fof(f2,axiom,(
% 4.08/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.08/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.02  
% 4.08/1.02  fof(f17,plain,(
% 4.08/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.08/1.02    inference(ennf_transformation,[],[f2])).
% 4.08/1.02  
% 4.08/1.02  fof(f51,plain,(
% 4.08/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.08/1.02    inference(cnf_transformation,[],[f17])).
% 4.08/1.02  
% 4.08/1.02  fof(f98,plain,(
% 4.08/1.02    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  fof(f102,plain,(
% 4.08/1.02    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  fof(f106,plain,(
% 4.08/1.02    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  fof(f114,plain,(
% 4.08/1.02    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  fof(f118,plain,(
% 4.08/1.02    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  fof(f122,plain,(
% 4.08/1.02    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  fof(f39,plain,(
% 4.08/1.02    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 4.08/1.02    inference(nnf_transformation,[],[f33])).
% 4.08/1.02  
% 4.08/1.02  fof(f40,plain,(
% 4.08/1.02    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 4.08/1.02    inference(flattening,[],[f39])).
% 4.08/1.02  
% 4.08/1.02  fof(f41,plain,(
% 4.08/1.02    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) & ((m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 4.08/1.02    inference(rectify,[],[f40])).
% 4.08/1.02  
% 4.08/1.02  fof(f75,plain,(
% 4.08/1.02    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) )),
% 4.08/1.02    inference(cnf_transformation,[],[f41])).
% 4.08/1.02  
% 4.08/1.02  fof(f6,axiom,(
% 4.08/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 4.08/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.02  
% 4.08/1.02  fof(f22,plain,(
% 4.08/1.02    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.08/1.02    inference(ennf_transformation,[],[f6])).
% 4.08/1.02  
% 4.08/1.02  fof(f55,plain,(
% 4.08/1.02    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.08/1.02    inference(cnf_transformation,[],[f22])).
% 4.08/1.02  
% 4.08/1.02  fof(f69,plain,(
% 4.08/1.02    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 4.08/1.02    inference(cnf_transformation,[],[f41])).
% 4.08/1.02  
% 4.08/1.02  fof(f73,plain,(
% 4.08/1.02    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 4.08/1.02    inference(cnf_transformation,[],[f41])).
% 4.08/1.02  
% 4.08/1.02  fof(f124,plain,(
% 4.08/1.02    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 4.08/1.02    inference(cnf_transformation,[],[f49])).
% 4.08/1.02  
% 4.08/1.02  cnf(c_61,negated_conjecture,
% 4.08/1.02      ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
% 4.08/1.02      inference(cnf_transformation,[],[f90]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2373,negated_conjecture,
% 4.08/1.02      ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
% 4.08/1.02      inference(subtyping,[status(esa)],[c_61]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_7,plain,
% 4.08/1.02      ( ~ m1_pre_topc(X0,X1)
% 4.08/1.02      | ~ m1_pre_topc(X2,X1)
% 4.08/1.02      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 4.08/1.02      | v2_struct_0(X1)
% 4.08/1.02      | v2_struct_0(X0)
% 4.08/1.02      | v2_struct_0(X2)
% 4.08/1.02      | ~ l1_pre_topc(X1) ),
% 4.08/1.02      inference(cnf_transformation,[],[f58]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2395,plain,
% 4.08/1.02      ( ~ m1_pre_topc(X0_54,X1_54)
% 4.08/1.02      | ~ m1_pre_topc(X2_54,X1_54)
% 4.08/1.02      | m1_pre_topc(k1_tsep_1(X1_54,X0_54,X2_54),X1_54)
% 4.08/1.02      | v2_struct_0(X0_54)
% 4.08/1.02      | v2_struct_0(X1_54)
% 4.08/1.02      | v2_struct_0(X2_54)
% 4.08/1.02      | ~ l1_pre_topc(X1_54) ),
% 4.08/1.02      inference(subtyping,[status(esa)],[c_7]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3249,plain,
% 4.08/1.02      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 4.08/1.02      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 4.08/1.02      | m1_pre_topc(k1_tsep_1(X1_54,X0_54,X2_54),X1_54) = iProver_top
% 4.08/1.02      | v2_struct_0(X1_54) = iProver_top
% 4.08/1.02      | v2_struct_0(X0_54) = iProver_top
% 4.08/1.02      | v2_struct_0(X2_54) = iProver_top
% 4.08/1.02      | l1_pre_topc(X1_54) != iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_2395]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_5467,plain,
% 4.08/1.02      ( m1_pre_topc(sK5,sK2) != iProver_top
% 4.08/1.02      | m1_pre_topc(sK6,sK2) != iProver_top
% 4.08/1.02      | m1_pre_topc(sK2,sK2) = iProver_top
% 4.08/1.02      | v2_struct_0(sK5) = iProver_top
% 4.08/1.02      | v2_struct_0(sK6) = iProver_top
% 4.08/1.02      | v2_struct_0(sK2) = iProver_top
% 4.08/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_2373,c_3249]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_74,negated_conjecture,
% 4.08/1.02      ( ~ v2_struct_0(sK2) ),
% 4.08/1.02      inference(cnf_transformation,[],[f77]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_75,plain,
% 4.08/1.02      ( v2_struct_0(sK2) != iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_74]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_72,negated_conjecture,
% 4.08/1.02      ( l1_pre_topc(sK2) ),
% 4.08/1.02      inference(cnf_transformation,[],[f79]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_77,plain,
% 4.08/1.02      ( l1_pre_topc(sK2) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_72]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_65,negated_conjecture,
% 4.08/1.02      ( ~ v2_struct_0(sK5) ),
% 4.08/1.02      inference(cnf_transformation,[],[f86]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_84,plain,
% 4.08/1.02      ( v2_struct_0(sK5) != iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_65]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_64,negated_conjecture,
% 4.08/1.02      ( m1_pre_topc(sK5,sK2) ),
% 4.08/1.02      inference(cnf_transformation,[],[f87]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_85,plain,
% 4.08/1.02      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_64]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_63,negated_conjecture,
% 4.08/1.02      ( ~ v2_struct_0(sK6) ),
% 4.08/1.02      inference(cnf_transformation,[],[f88]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_86,plain,
% 4.08/1.02      ( v2_struct_0(sK6) != iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_63]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_62,negated_conjecture,
% 4.08/1.02      ( m1_pre_topc(sK6,sK2) ),
% 4.08/1.02      inference(cnf_transformation,[],[f89]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_87,plain,
% 4.08/1.02      ( m1_pre_topc(sK6,sK2) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3430,plain,
% 4.08/1.02      ( ~ m1_pre_topc(X0_54,X1_54)
% 4.08/1.02      | m1_pre_topc(k1_tsep_1(X1_54,sK5,X0_54),X1_54)
% 4.08/1.02      | ~ m1_pre_topc(sK5,X1_54)
% 4.08/1.02      | v2_struct_0(X1_54)
% 4.08/1.02      | v2_struct_0(X0_54)
% 4.08/1.02      | v2_struct_0(sK5)
% 4.08/1.02      | ~ l1_pre_topc(X1_54) ),
% 4.08/1.02      inference(instantiation,[status(thm)],[c_2395]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3579,plain,
% 4.08/1.02      ( ~ m1_pre_topc(X0_54,sK2)
% 4.08/1.02      | m1_pre_topc(k1_tsep_1(sK2,sK5,X0_54),sK2)
% 4.08/1.02      | ~ m1_pre_topc(sK5,sK2)
% 4.08/1.02      | v2_struct_0(X0_54)
% 4.08/1.02      | v2_struct_0(sK5)
% 4.08/1.02      | v2_struct_0(sK2)
% 4.08/1.02      | ~ l1_pre_topc(sK2) ),
% 4.08/1.02      inference(instantiation,[status(thm)],[c_3430]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3848,plain,
% 4.08/1.02      ( m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2)
% 4.08/1.02      | ~ m1_pre_topc(sK5,sK2)
% 4.08/1.02      | ~ m1_pre_topc(sK6,sK2)
% 4.08/1.02      | v2_struct_0(sK5)
% 4.08/1.02      | v2_struct_0(sK6)
% 4.08/1.02      | v2_struct_0(sK2)
% 4.08/1.02      | ~ l1_pre_topc(sK2) ),
% 4.08/1.02      inference(instantiation,[status(thm)],[c_3579]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3849,plain,
% 4.08/1.02      ( m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2) = iProver_top
% 4.08/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 4.08/1.02      | m1_pre_topc(sK6,sK2) != iProver_top
% 4.08/1.02      | v2_struct_0(sK5) = iProver_top
% 4.08/1.02      | v2_struct_0(sK6) = iProver_top
% 4.08/1.02      | v2_struct_0(sK2) = iProver_top
% 4.08/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_3848]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2401,plain,( X0_54 = X0_54 ),theory(equality) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3913,plain,
% 4.08/1.02      ( sK2 = sK2 ),
% 4.08/1.02      inference(instantiation,[status(thm)],[c_2401]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2406,plain,
% 4.08/1.02      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 4.08/1.02      theory(equality) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3759,plain,
% 4.08/1.02      ( X0_54 != X1_54 | sK2 != X1_54 | sK2 = X0_54 ),
% 4.08/1.02      inference(instantiation,[status(thm)],[c_2406]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3915,plain,
% 4.08/1.02      ( X0_54 != sK2 | sK2 = X0_54 | sK2 != sK2 ),
% 4.08/1.02      inference(instantiation,[status(thm)],[c_3759]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_4347,plain,
% 4.08/1.02      ( k1_tsep_1(sK2,sK5,sK6) != sK2
% 4.08/1.02      | sK2 = k1_tsep_1(sK2,sK5,sK6)
% 4.08/1.02      | sK2 != sK2 ),
% 4.08/1.02      inference(instantiation,[status(thm)],[c_3915]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2414,plain,
% 4.08/1.02      ( ~ m1_pre_topc(X0_54,X1_54)
% 4.08/1.02      | m1_pre_topc(X2_54,X3_54)
% 4.08/1.02      | X2_54 != X0_54
% 4.08/1.02      | X3_54 != X1_54 ),
% 4.08/1.02      theory(equality) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3601,plain,
% 4.08/1.02      ( ~ m1_pre_topc(X0_54,X1_54)
% 4.08/1.02      | m1_pre_topc(X2_54,sK2)
% 4.08/1.02      | X2_54 != X0_54
% 4.08/1.02      | sK2 != X1_54 ),
% 4.08/1.02      inference(instantiation,[status(thm)],[c_2414]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3790,plain,
% 4.08/1.02      ( ~ m1_pre_topc(X0_54,sK2)
% 4.08/1.02      | m1_pre_topc(X1_54,sK2)
% 4.08/1.02      | X1_54 != X0_54
% 4.08/1.02      | sK2 != sK2 ),
% 4.08/1.02      inference(instantiation,[status(thm)],[c_3601]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_4279,plain,
% 4.08/1.02      ( m1_pre_topc(X0_54,sK2)
% 4.08/1.02      | ~ m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2)
% 4.08/1.02      | X0_54 != k1_tsep_1(sK2,sK5,sK6)
% 4.08/1.02      | sK2 != sK2 ),
% 4.08/1.02      inference(instantiation,[status(thm)],[c_3790]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_5007,plain,
% 4.08/1.02      ( ~ m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2)
% 4.08/1.02      | m1_pre_topc(sK2,sK2)
% 4.08/1.02      | sK2 != k1_tsep_1(sK2,sK5,sK6)
% 4.08/1.02      | sK2 != sK2 ),
% 4.08/1.02      inference(instantiation,[status(thm)],[c_4279]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_5008,plain,
% 4.08/1.02      ( sK2 != k1_tsep_1(sK2,sK5,sK6)
% 4.08/1.02      | sK2 != sK2
% 4.08/1.02      | m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2) != iProver_top
% 4.08/1.02      | m1_pre_topc(sK2,sK2) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_5007]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_6222,plain,
% 4.08/1.02      ( m1_pre_topc(sK2,sK2) = iProver_top ),
% 4.08/1.02      inference(global_propositional_subsumption,
% 4.08/1.02                [status(thm)],
% 4.08/1.02                [c_5467,c_75,c_77,c_84,c_85,c_86,c_87,c_2373,c_3849,
% 4.08/1.02                 c_3913,c_4347,c_5008]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_66,negated_conjecture,
% 4.08/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 4.08/1.02      inference(cnf_transformation,[],[f85]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2368,negated_conjecture,
% 4.08/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 4.08/1.02      inference(subtyping,[status(esa)],[c_66]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3275,plain,
% 4.08/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_2368]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_6,plain,
% 4.08/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.08/1.02      | ~ m1_pre_topc(X3,X1)
% 4.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.08/1.02      | v2_struct_0(X1)
% 4.08/1.02      | v2_struct_0(X2)
% 4.08/1.02      | ~ v2_pre_topc(X2)
% 4.08/1.02      | ~ v2_pre_topc(X1)
% 4.08/1.02      | ~ l1_pre_topc(X1)
% 4.08/1.02      | ~ l1_pre_topc(X2)
% 4.08/1.02      | ~ v1_funct_1(X0)
% 4.08/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 4.08/1.02      inference(cnf_transformation,[],[f56]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2396,plain,
% 4.08/1.02      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 4.08/1.02      | ~ m1_pre_topc(X2_54,X0_54)
% 4.08/1.02      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 4.08/1.02      | v2_struct_0(X0_54)
% 4.08/1.02      | v2_struct_0(X1_54)
% 4.08/1.02      | ~ v2_pre_topc(X0_54)
% 4.08/1.02      | ~ v2_pre_topc(X1_54)
% 4.08/1.02      | ~ l1_pre_topc(X0_54)
% 4.08/1.02      | ~ l1_pre_topc(X1_54)
% 4.08/1.02      | ~ v1_funct_1(X0_55)
% 4.08/1.02      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_55,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_55,X2_54) ),
% 4.08/1.02      inference(subtyping,[status(esa)],[c_6]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3248,plain,
% 4.08/1.02      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_55,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_55,X2_54)
% 4.08/1.02      | v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.08/1.02      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 4.08/1.02      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.08/1.02      | v2_struct_0(X1_54) = iProver_top
% 4.08/1.02      | v2_struct_0(X0_54) = iProver_top
% 4.08/1.02      | v2_pre_topc(X1_54) != iProver_top
% 4.08/1.02      | v2_pre_topc(X0_54) != iProver_top
% 4.08/1.02      | l1_pre_topc(X1_54) != iProver_top
% 4.08/1.02      | l1_pre_topc(X0_54) != iProver_top
% 4.08/1.02      | v1_funct_1(X0_55) != iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_2396]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_4542,plain,
% 4.08/1.02      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK3,sK4,X0_54)
% 4.08/1.02      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | m1_pre_topc(X0_54,sK2) != iProver_top
% 4.08/1.02      | v2_struct_0(sK3) = iProver_top
% 4.08/1.02      | v2_struct_0(sK2) = iProver_top
% 4.08/1.02      | v2_pre_topc(sK3) != iProver_top
% 4.08/1.02      | v2_pre_topc(sK2) != iProver_top
% 4.08/1.02      | l1_pre_topc(sK3) != iProver_top
% 4.08/1.02      | l1_pre_topc(sK2) != iProver_top
% 4.08/1.02      | v1_funct_1(sK4) != iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_3275,c_3248]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_73,negated_conjecture,
% 4.08/1.02      ( v2_pre_topc(sK2) ),
% 4.08/1.02      inference(cnf_transformation,[],[f78]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_76,plain,
% 4.08/1.02      ( v2_pre_topc(sK2) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_73]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_71,negated_conjecture,
% 4.08/1.02      ( ~ v2_struct_0(sK3) ),
% 4.08/1.02      inference(cnf_transformation,[],[f80]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_78,plain,
% 4.08/1.02      ( v2_struct_0(sK3) != iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_71]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_70,negated_conjecture,
% 4.08/1.02      ( v2_pre_topc(sK3) ),
% 4.08/1.02      inference(cnf_transformation,[],[f81]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_79,plain,
% 4.08/1.02      ( v2_pre_topc(sK3) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_70]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_69,negated_conjecture,
% 4.08/1.02      ( l1_pre_topc(sK3) ),
% 4.08/1.02      inference(cnf_transformation,[],[f82]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_80,plain,
% 4.08/1.02      ( l1_pre_topc(sK3) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_69]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_68,negated_conjecture,
% 4.08/1.02      ( v1_funct_1(sK4) ),
% 4.08/1.02      inference(cnf_transformation,[],[f83]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_81,plain,
% 4.08/1.02      ( v1_funct_1(sK4) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_68]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_67,negated_conjecture,
% 4.08/1.02      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 4.08/1.02      inference(cnf_transformation,[],[f84]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_82,plain,
% 4.08/1.02      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_67]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_6437,plain,
% 4.08/1.02      ( m1_pre_topc(X0_54,sK2) != iProver_top
% 4.08/1.02      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK3,sK4,X0_54) ),
% 4.08/1.02      inference(global_propositional_subsumption,
% 4.08/1.02                [status(thm)],
% 4.08/1.02                [c_4542,c_75,c_76,c_77,c_78,c_79,c_80,c_81,c_82]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_6438,plain,
% 4.08/1.02      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK3,sK4,X0_54)
% 4.08/1.02      | m1_pre_topc(X0_54,sK2) != iProver_top ),
% 4.08/1.02      inference(renaming,[status(thm)],[c_6437]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3,plain,
% 4.08/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.08/1.02      | ~ v1_funct_1(X0)
% 4.08/1.02      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 4.08/1.02      inference(cnf_transformation,[],[f53]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2399,plain,
% 4.08/1.02      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 4.08/1.02      | ~ v1_funct_1(X0_55)
% 4.08/1.02      | k2_partfun1(X0_56,X1_56,X0_55,X2_56) = k7_relat_1(X0_55,X2_56) ),
% 4.08/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3245,plain,
% 4.08/1.02      ( k2_partfun1(X0_56,X1_56,X0_55,X2_56) = k7_relat_1(X0_55,X2_56)
% 4.08/1.02      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 4.08/1.02      | v1_funct_1(X0_55) != iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_2399]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3830,plain,
% 4.08/1.02      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_56) = k7_relat_1(sK4,X0_56)
% 4.08/1.02      | v1_funct_1(sK4) != iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_3275,c_3245]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_5098,plain,
% 4.08/1.02      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_56) = k7_relat_1(sK4,X0_56) ),
% 4.08/1.02      inference(global_propositional_subsumption,
% 4.08/1.02                [status(thm)],
% 4.08/1.02                [c_3830,c_81]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_6443,plain,
% 4.08/1.02      ( k2_tmap_1(sK2,sK3,sK4,X0_54) = k7_relat_1(sK4,u1_struct_0(X0_54))
% 4.08/1.02      | m1_pre_topc(X0_54,sK2) != iProver_top ),
% 4.08/1.02      inference(demodulation,[status(thm)],[c_6438,c_5098]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_6450,plain,
% 4.08/1.02      ( k2_tmap_1(sK2,sK3,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_6222,c_6443]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_16,plain,
% 4.08/1.02      ( ~ sP1(X0,X1,X2,X3,X4)
% 4.08/1.02      | sP0(X4,X3,X2,X1,X0)
% 4.08/1.02      | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
% 4.08/1.02      | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
% 4.08/1.02      | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
% 4.08/1.02      | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
% 4.08/1.02      inference(cnf_transformation,[],[f62]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_26,plain,
% 4.08/1.02      ( sP1(X0,X1,X2,X3,X4)
% 4.08/1.02      | ~ r4_tsep_1(X1,X0,X3)
% 4.08/1.02      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
% 4.08/1.02      | ~ m1_pre_topc(X3,X1)
% 4.08/1.02      | ~ m1_pre_topc(X0,X1)
% 4.08/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 4.08/1.02      | v2_struct_0(X1)
% 4.08/1.02      | v2_struct_0(X4)
% 4.08/1.02      | v2_struct_0(X0)
% 4.08/1.02      | v2_struct_0(X3)
% 4.08/1.02      | ~ v2_pre_topc(X4)
% 4.08/1.02      | ~ v2_pre_topc(X1)
% 4.08/1.02      | ~ l1_pre_topc(X1)
% 4.08/1.02      | ~ l1_pre_topc(X4)
% 4.08/1.02      | ~ v1_funct_1(X2) ),
% 4.08/1.02      inference(cnf_transformation,[],[f76]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_60,negated_conjecture,
% 4.08/1.02      ( r4_tsep_1(sK2,sK5,sK6) ),
% 4.08/1.02      inference(cnf_transformation,[],[f91]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_772,plain,
% 4.08/1.02      ( sP1(X0,X1,X2,X3,X4)
% 4.08/1.02      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
% 4.08/1.02      | ~ m1_pre_topc(X0,X1)
% 4.08/1.02      | ~ m1_pre_topc(X3,X1)
% 4.08/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 4.08/1.02      | v2_struct_0(X1)
% 4.08/1.02      | v2_struct_0(X0)
% 4.08/1.02      | v2_struct_0(X3)
% 4.08/1.02      | v2_struct_0(X4)
% 4.08/1.02      | ~ v2_pre_topc(X1)
% 4.08/1.02      | ~ v2_pre_topc(X4)
% 4.08/1.02      | ~ l1_pre_topc(X1)
% 4.08/1.02      | ~ l1_pre_topc(X4)
% 4.08/1.02      | ~ v1_funct_1(X2)
% 4.08/1.02      | sK5 != X0
% 4.08/1.02      | sK6 != X3
% 4.08/1.02      | sK2 != X1 ),
% 4.08/1.02      inference(resolution_lifted,[status(thm)],[c_26,c_60]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_773,plain,
% 4.08/1.02      ( sP1(sK5,sK2,X0,sK6,X1)
% 4.08/1.02      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 4.08/1.02      | ~ m1_pre_topc(sK5,sK2)
% 4.08/1.02      | ~ m1_pre_topc(sK6,sK2)
% 4.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 4.08/1.02      | v2_struct_0(X1)
% 4.08/1.02      | v2_struct_0(sK5)
% 4.08/1.02      | v2_struct_0(sK6)
% 4.08/1.02      | v2_struct_0(sK2)
% 4.08/1.02      | ~ v2_pre_topc(X1)
% 4.08/1.02      | ~ v2_pre_topc(sK2)
% 4.08/1.02      | ~ l1_pre_topc(X1)
% 4.08/1.02      | ~ l1_pre_topc(sK2)
% 4.08/1.02      | ~ v1_funct_1(X0) ),
% 4.08/1.02      inference(unflattening,[status(thm)],[c_772]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_777,plain,
% 4.08/1.02      ( ~ l1_pre_topc(X1)
% 4.08/1.02      | v2_struct_0(X1)
% 4.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 4.08/1.02      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 4.08/1.02      | sP1(sK5,sK2,X0,sK6,X1)
% 4.08/1.02      | ~ v2_pre_topc(X1)
% 4.08/1.02      | ~ v1_funct_1(X0) ),
% 4.08/1.02      inference(global_propositional_subsumption,
% 4.08/1.02                [status(thm)],
% 4.08/1.02                [c_773,c_74,c_73,c_72,c_65,c_64,c_63,c_62]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_778,plain,
% 4.08/1.02      ( sP1(sK5,sK2,X0,sK6,X1)
% 4.08/1.02      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 4.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 4.08/1.02      | v2_struct_0(X1)
% 4.08/1.02      | ~ v2_pre_topc(X1)
% 4.08/1.02      | ~ l1_pre_topc(X1)
% 4.08/1.02      | ~ v1_funct_1(X0) ),
% 4.08/1.02      inference(renaming,[status(thm)],[c_777]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_813,plain,
% 4.08/1.02      ( sP0(X0,X1,X2,X3,X4)
% 4.08/1.02      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_tsep_1(X3,X4,X1),X0)
% 4.08/1.02      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 4.08/1.02      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))
% 4.08/1.02      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 4.08/1.02      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))))
% 4.08/1.02      | v2_struct_0(X6)
% 4.08/1.02      | ~ v2_pre_topc(X6)
% 4.08/1.02      | ~ l1_pre_topc(X6)
% 4.08/1.02      | ~ v1_funct_1(X5)
% 4.08/1.02      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)))
% 4.08/1.02      | X5 != X2
% 4.08/1.02      | X6 != X0
% 4.08/1.02      | sK5 != X4
% 4.08/1.02      | sK6 != X1
% 4.08/1.02      | sK2 != X3 ),
% 4.08/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_778]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_814,plain,
% 4.08/1.02      ( sP0(X0,sK6,X1,sK2,sK5)
% 4.08/1.02      | ~ v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
% 4.08/1.02      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 4.08/1.02      | ~ v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))
% 4.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 4.08/1.02      | ~ m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
% 4.08/1.02      | v2_struct_0(X0)
% 4.08/1.02      | ~ v2_pre_topc(X0)
% 4.08/1.02      | ~ l1_pre_topc(X0)
% 4.08/1.02      | ~ v1_funct_1(X1)
% 4.08/1.02      | ~ v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) ),
% 4.08/1.02      inference(unflattening,[status(thm)],[c_813]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2357,plain,
% 4.08/1.02      ( sP0(X0_54,sK6,X0_55,sK2,sK5)
% 4.08/1.02      | ~ v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_54)
% 4.08/1.02      | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
% 4.08/1.02      | ~ v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54))
% 4.08/1.02      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
% 4.08/1.02      | ~ m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54))))
% 4.08/1.02      | v2_struct_0(X0_54)
% 4.08/1.02      | ~ v2_pre_topc(X0_54)
% 4.08/1.02      | ~ l1_pre_topc(X0_54)
% 4.08/1.02      | ~ v1_funct_1(X0_55)
% 4.08/1.02      | ~ v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6))) ),
% 4.08/1.02      inference(subtyping,[status(esa)],[c_814]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3286,plain,
% 4.08/1.02      ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_54) != iProver_top
% 4.08/1.02      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 4.08/1.02      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54)) != iProver_top
% 4.08/1.02      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 4.08/1.02      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54)))) != iProver_top
% 4.08/1.02      | v2_struct_0(X0_54) = iProver_top
% 4.08/1.02      | v2_pre_topc(X0_54) != iProver_top
% 4.08/1.02      | l1_pre_topc(X0_54) != iProver_top
% 4.08/1.02      | v1_funct_1(X0_55) != iProver_top
% 4.08/1.02      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6))) != iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_2357]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3295,plain,
% 4.08/1.02      ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) != iProver_top
% 4.08/1.02      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 4.08/1.02      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 4.08/1.02      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 4.08/1.02      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 4.08/1.02      | v2_struct_0(X0_54) = iProver_top
% 4.08/1.02      | v2_pre_topc(X0_54) != iProver_top
% 4.08/1.02      | l1_pre_topc(X0_54) != iProver_top
% 4.08/1.02      | v1_funct_1(X0_55) != iProver_top
% 4.08/1.02      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) != iProver_top ),
% 4.08/1.02      inference(light_normalisation,[status(thm)],[c_3286,c_2373]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_6935,plain,
% 4.08/1.02      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
% 4.08/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | v2_struct_0(sK3) = iProver_top
% 4.08/1.02      | v2_pre_topc(sK3) != iProver_top
% 4.08/1.02      | l1_pre_topc(sK3) != iProver_top
% 4.08/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
% 4.08/1.02      | v1_funct_1(sK4) != iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_6450,c_3295]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_6938,plain,
% 4.08/1.02      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 4.08/1.02      | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK2)),sK2,sK3) != iProver_top
% 4.08/1.02      | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | v2_struct_0(sK3) = iProver_top
% 4.08/1.02      | v2_pre_topc(sK3) != iProver_top
% 4.08/1.02      | l1_pre_topc(sK3) != iProver_top
% 4.08/1.02      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
% 4.08/1.02      | v1_funct_1(sK4) != iProver_top ),
% 4.08/1.02      inference(light_normalisation,[status(thm)],[c_6935,c_6450]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_83,plain,
% 4.08/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_66]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_12,plain,
% 4.08/1.02      ( ~ sP1(X0,X1,X2,X3,X4)
% 4.08/1.02      | ~ sP0(X4,X3,X2,X1,X0)
% 4.08/1.02      | m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) ),
% 4.08/1.02      inference(cnf_transformation,[],[f66]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_942,plain,
% 4.08/1.02      ( ~ sP0(X0,X1,X2,X3,X4)
% 4.08/1.02      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 4.08/1.02      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 4.08/1.02      | m1_subset_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))))
% 4.08/1.02      | v2_struct_0(X6)
% 4.08/1.02      | ~ v2_pre_topc(X6)
% 4.08/1.02      | ~ l1_pre_topc(X6)
% 4.08/1.02      | ~ v1_funct_1(X5)
% 4.08/1.02      | X5 != X2
% 4.08/1.02      | X6 != X0
% 4.08/1.02      | sK5 != X4
% 4.08/1.02      | sK6 != X1
% 4.08/1.02      | sK2 != X3 ),
% 4.08/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_778]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_943,plain,
% 4.08/1.02      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 4.08/1.02      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 4.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 4.08/1.02      | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
% 4.08/1.02      | v2_struct_0(X0)
% 4.08/1.02      | ~ v2_pre_topc(X0)
% 4.08/1.02      | ~ l1_pre_topc(X0)
% 4.08/1.02      | ~ v1_funct_1(X1) ),
% 4.08/1.02      inference(unflattening,[status(thm)],[c_942]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2353,plain,
% 4.08/1.02      ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
% 4.08/1.02      | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
% 4.08/1.02      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
% 4.08/1.02      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54))))
% 4.08/1.02      | v2_struct_0(X0_54)
% 4.08/1.02      | ~ v2_pre_topc(X0_54)
% 4.08/1.02      | ~ l1_pre_topc(X0_54)
% 4.08/1.02      | ~ v1_funct_1(X0_55) ),
% 4.08/1.02      inference(subtyping,[status(esa)],[c_943]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3290,plain,
% 4.08/1.02      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 4.08/1.02      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 4.08/1.02      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 4.08/1.02      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54)))) = iProver_top
% 4.08/1.02      | v2_struct_0(X0_54) = iProver_top
% 4.08/1.02      | v2_pre_topc(X0_54) != iProver_top
% 4.08/1.02      | l1_pre_topc(X0_54) != iProver_top
% 4.08/1.02      | v1_funct_1(X0_55) != iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_2353]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3294,plain,
% 4.08/1.02      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 4.08/1.02      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 4.08/1.02      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 4.08/1.02      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) = iProver_top
% 4.08/1.02      | v2_struct_0(X0_54) = iProver_top
% 4.08/1.02      | v2_pre_topc(X0_54) != iProver_top
% 4.08/1.02      | l1_pre_topc(X0_54) != iProver_top
% 4.08/1.02      | v1_funct_1(X0_55) != iProver_top ),
% 4.08/1.02      inference(light_normalisation,[status(thm)],[c_3290,c_2373]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_6936,plain,
% 4.08/1.02      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 4.08/1.02      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top
% 4.08/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | v2_struct_0(sK3) = iProver_top
% 4.08/1.02      | v2_pre_topc(sK3) != iProver_top
% 4.08/1.02      | l1_pre_topc(sK3) != iProver_top
% 4.08/1.02      | v1_funct_1(sK4) != iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_6450,c_3294]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_4,plain,
% 4.08/1.02      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 4.08/1.02      inference(cnf_transformation,[],[f54]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_178,plain,
% 4.08/1.02      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_180,plain,
% 4.08/1.02      ( l1_pre_topc(sK3) != iProver_top
% 4.08/1.02      | l1_struct_0(sK3) = iProver_top ),
% 4.08/1.02      inference(instantiation,[status(thm)],[c_178]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2398,plain,
% 4.08/1.02      ( ~ l1_pre_topc(X0_54) | l1_struct_0(X0_54) ),
% 4.08/1.02      inference(subtyping,[status(esa)],[c_4]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3678,plain,
% 4.08/1.02      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 4.08/1.02      inference(instantiation,[status(thm)],[c_2398]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3679,plain,
% 4.08/1.02      ( l1_pre_topc(sK2) != iProver_top
% 4.08/1.02      | l1_struct_0(sK2) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_3678]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_9,plain,
% 4.08/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.08/1.02      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 4.08/1.02      | ~ l1_struct_0(X3)
% 4.08/1.02      | ~ l1_struct_0(X2)
% 4.08/1.02      | ~ l1_struct_0(X1)
% 4.08/1.02      | ~ v1_funct_1(X0) ),
% 4.08/1.02      inference(cnf_transformation,[],[f61]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2393,plain,
% 4.08/1.02      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 4.08/1.02      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 4.08/1.02      | m1_subset_1(k2_tmap_1(X0_54,X1_54,X0_55,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 4.08/1.02      | ~ l1_struct_0(X2_54)
% 4.08/1.02      | ~ l1_struct_0(X1_54)
% 4.08/1.02      | ~ l1_struct_0(X0_54)
% 4.08/1.02      | ~ v1_funct_1(X0_55) ),
% 4.08/1.02      inference(subtyping,[status(esa)],[c_9]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3251,plain,
% 4.08/1.02      ( v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.08/1.02      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.08/1.02      | m1_subset_1(k2_tmap_1(X0_54,X1_54,X0_55,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) = iProver_top
% 4.08/1.02      | l1_struct_0(X2_54) != iProver_top
% 4.08/1.02      | l1_struct_0(X1_54) != iProver_top
% 4.08/1.02      | l1_struct_0(X0_54) != iProver_top
% 4.08/1.02      | v1_funct_1(X0_55) != iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_2393]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_8535,plain,
% 4.08/1.02      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top
% 4.08/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | l1_struct_0(sK3) != iProver_top
% 4.08/1.02      | l1_struct_0(sK2) != iProver_top
% 4.08/1.02      | v1_funct_1(sK4) != iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_6450,c_3251]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_8929,plain,
% 4.08/1.02      ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 4.08/1.02      inference(global_propositional_subsumption,
% 4.08/1.02                [status(thm)],
% 4.08/1.02                [c_6936,c_77,c_80,c_81,c_82,c_83,c_180,c_3679,c_8535]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_13,plain,
% 4.08/1.02      ( ~ sP1(X0,X1,X2,X3,X4)
% 4.08/1.02      | ~ sP0(X4,X3,X2,X1,X0)
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) ),
% 4.08/1.02      inference(cnf_transformation,[],[f65]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_912,plain,
% 4.08/1.02      ( ~ sP0(X0,X1,X2,X3,X4)
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_tsep_1(X3,X4,X1),X0)
% 4.08/1.02      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 4.08/1.02      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 4.08/1.02      | v2_struct_0(X6)
% 4.08/1.02      | ~ v2_pre_topc(X6)
% 4.08/1.02      | ~ l1_pre_topc(X6)
% 4.08/1.02      | ~ v1_funct_1(X5)
% 4.08/1.02      | X5 != X2
% 4.08/1.02      | X6 != X0
% 4.08/1.02      | sK5 != X4
% 4.08/1.02      | sK6 != X1
% 4.08/1.02      | sK2 != X3 ),
% 4.08/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_778]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_913,plain,
% 4.08/1.02      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
% 4.08/1.02      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 4.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 4.08/1.02      | v2_struct_0(X0)
% 4.08/1.02      | ~ v2_pre_topc(X0)
% 4.08/1.02      | ~ l1_pre_topc(X0)
% 4.08/1.02      | ~ v1_funct_1(X1) ),
% 4.08/1.02      inference(unflattening,[status(thm)],[c_912]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2354,plain,
% 4.08/1.02      ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_54)
% 4.08/1.02      | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
% 4.08/1.02      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
% 4.08/1.02      | v2_struct_0(X0_54)
% 4.08/1.02      | ~ v2_pre_topc(X0_54)
% 4.08/1.02      | ~ l1_pre_topc(X0_54)
% 4.08/1.02      | ~ v1_funct_1(X0_55) ),
% 4.08/1.02      inference(subtyping,[status(esa)],[c_913]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3289,plain,
% 4.08/1.02      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_54) = iProver_top
% 4.08/1.02      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 4.08/1.02      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 4.08/1.02      | v2_struct_0(X0_54) = iProver_top
% 4.08/1.02      | v2_pre_topc(X0_54) != iProver_top
% 4.08/1.02      | l1_pre_topc(X0_54) != iProver_top
% 4.08/1.02      | v1_funct_1(X0_55) != iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_2354]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3292,plain,
% 4.08/1.02      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) = iProver_top
% 4.08/1.02      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 4.08/1.02      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 4.08/1.02      | v2_struct_0(X0_54) = iProver_top
% 4.08/1.02      | v2_pre_topc(X0_54) != iProver_top
% 4.08/1.02      | l1_pre_topc(X0_54) != iProver_top
% 4.08/1.02      | v1_funct_1(X0_55) != iProver_top ),
% 4.08/1.02      inference(light_normalisation,[status(thm)],[c_3289,c_2373]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_8933,plain,
% 4.08/1.02      ( sP0(sK3,sK6,k7_relat_1(sK4,u1_struct_0(sK2)),sK2,sK5) != iProver_top
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(sK2,sK3,k7_relat_1(sK4,u1_struct_0(sK2)),sK2),sK2,sK3) = iProver_top
% 4.08/1.02      | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | v2_struct_0(sK3) = iProver_top
% 4.08/1.02      | v2_pre_topc(sK3) != iProver_top
% 4.08/1.02      | l1_pre_topc(sK3) != iProver_top
% 4.08/1.02      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_8929,c_3292]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_10,plain,
% 4.08/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.08/1.02      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 4.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.08/1.02      | ~ l1_struct_0(X3)
% 4.08/1.02      | ~ l1_struct_0(X2)
% 4.08/1.02      | ~ l1_struct_0(X1)
% 4.08/1.02      | ~ v1_funct_1(X0) ),
% 4.08/1.02      inference(cnf_transformation,[],[f60]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2392,plain,
% 4.08/1.02      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 4.08/1.02      | v1_funct_2(k2_tmap_1(X0_54,X1_54,X0_55,X2_54),u1_struct_0(X2_54),u1_struct_0(X1_54))
% 4.08/1.02      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 4.08/1.02      | ~ l1_struct_0(X2_54)
% 4.08/1.02      | ~ l1_struct_0(X1_54)
% 4.08/1.02      | ~ l1_struct_0(X0_54)
% 4.08/1.02      | ~ v1_funct_1(X0_55) ),
% 4.08/1.02      inference(subtyping,[status(esa)],[c_10]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3252,plain,
% 4.08/1.02      ( v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.08/1.02      | v1_funct_2(k2_tmap_1(X0_54,X1_54,X0_55,X2_54),u1_struct_0(X2_54),u1_struct_0(X1_54)) = iProver_top
% 4.08/1.02      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.08/1.02      | l1_struct_0(X2_54) != iProver_top
% 4.08/1.02      | l1_struct_0(X1_54) != iProver_top
% 4.08/1.02      | l1_struct_0(X0_54) != iProver_top
% 4.08/1.02      | v1_funct_1(X0_55) != iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_2392]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_8666,plain,
% 4.08/1.02      ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
% 4.08/1.02      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | l1_struct_0(sK3) != iProver_top
% 4.08/1.02      | l1_struct_0(sK2) != iProver_top
% 4.08/1.02      | v1_funct_1(sK4) != iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_6450,c_3252]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_11,plain,
% 4.08/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.08/1.02      | ~ l1_struct_0(X3)
% 4.08/1.02      | ~ l1_struct_0(X2)
% 4.08/1.02      | ~ l1_struct_0(X1)
% 4.08/1.02      | ~ v1_funct_1(X0)
% 4.08/1.02      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 4.08/1.02      inference(cnf_transformation,[],[f59]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2391,plain,
% 4.08/1.02      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 4.08/1.02      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 4.08/1.02      | ~ l1_struct_0(X2_54)
% 4.08/1.02      | ~ l1_struct_0(X1_54)
% 4.08/1.02      | ~ l1_struct_0(X0_54)
% 4.08/1.02      | ~ v1_funct_1(X0_55)
% 4.08/1.02      | v1_funct_1(k2_tmap_1(X0_54,X1_54,X0_55,X2_54)) ),
% 4.08/1.02      inference(subtyping,[status(esa)],[c_11]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3253,plain,
% 4.08/1.02      ( v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.08/1.02      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.08/1.02      | l1_struct_0(X2_54) != iProver_top
% 4.08/1.02      | l1_struct_0(X1_54) != iProver_top
% 4.08/1.02      | l1_struct_0(X0_54) != iProver_top
% 4.08/1.02      | v1_funct_1(X0_55) != iProver_top
% 4.08/1.02      | v1_funct_1(k2_tmap_1(X0_54,X1_54,X0_55,X2_54)) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_2391]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_8560,plain,
% 4.08/1.02      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | l1_struct_0(X0_54) != iProver_top
% 4.08/1.02      | l1_struct_0(sK3) != iProver_top
% 4.08/1.02      | l1_struct_0(sK2) != iProver_top
% 4.08/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54)) = iProver_top
% 4.08/1.02      | v1_funct_1(sK4) != iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_3275,c_3253]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_8784,plain,
% 4.08/1.02      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54)) = iProver_top
% 4.08/1.02      | l1_struct_0(X0_54) != iProver_top ),
% 4.08/1.02      inference(global_propositional_subsumption,
% 4.08/1.02                [status(thm)],
% 4.08/1.02                [c_8560,c_77,c_80,c_81,c_82,c_180,c_3679]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_8785,plain,
% 4.08/1.02      ( l1_struct_0(X0_54) != iProver_top
% 4.08/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54)) = iProver_top ),
% 4.08/1.02      inference(renaming,[status(thm)],[c_8784]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_8792,plain,
% 4.08/1.02      ( l1_struct_0(sK2) != iProver_top
% 4.08/1.02      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_6450,c_8785]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_9102,plain,
% 4.08/1.02      ( v5_pre_topc(k2_tmap_1(sK2,sK3,k7_relat_1(sK4,u1_struct_0(sK2)),sK2),sK2,sK3) = iProver_top
% 4.08/1.02      | sP0(sK3,sK6,k7_relat_1(sK4,u1_struct_0(sK2)),sK2,sK5) != iProver_top ),
% 4.08/1.02      inference(global_propositional_subsumption,
% 4.08/1.02                [status(thm)],
% 4.08/1.02                [c_8933,c_77,c_78,c_79,c_80,c_81,c_82,c_83,c_180,c_3679,
% 4.08/1.02                 c_8666,c_8792]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_9103,plain,
% 4.08/1.02      ( sP0(sK3,sK6,k7_relat_1(sK4,u1_struct_0(sK2)),sK2,sK5) != iProver_top
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(sK2,sK3,k7_relat_1(sK4,u1_struct_0(sK2)),sK2),sK2,sK3) = iProver_top ),
% 4.08/1.02      inference(renaming,[status(thm)],[c_9102]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2,plain,
% 4.08/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.08/1.02      | v4_relat_1(X0,X1) ),
% 4.08/1.02      inference(cnf_transformation,[],[f52]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_0,plain,
% 4.08/1.02      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 4.08/1.02      inference(cnf_transformation,[],[f50]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_752,plain,
% 4.08/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.08/1.02      | ~ v1_relat_1(X0)
% 4.08/1.02      | k7_relat_1(X0,X1) = X0 ),
% 4.08/1.02      inference(resolution,[status(thm)],[c_2,c_0]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_1,plain,
% 4.08/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.08/1.02      | v1_relat_1(X0) ),
% 4.08/1.02      inference(cnf_transformation,[],[f51]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_756,plain,
% 4.08/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.08/1.02      | k7_relat_1(X0,X1) = X0 ),
% 4.08/1.02      inference(global_propositional_subsumption,
% 4.08/1.02                [status(thm)],
% 4.08/1.02                [c_752,c_2,c_1,c_0]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2358,plain,
% 4.08/1.02      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 4.08/1.02      | k7_relat_1(X0_55,X0_56) = X0_55 ),
% 4.08/1.02      inference(subtyping,[status(esa)],[c_756]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3285,plain,
% 4.08/1.02      ( k7_relat_1(X0_55,X0_56) = X0_55
% 4.08/1.02      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_2358]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_8985,plain,
% 4.08/1.02      ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK4 ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_3275,c_3285]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_9035,plain,
% 4.08/1.02      ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4 ),
% 4.08/1.02      inference(demodulation,[status(thm)],[c_8985,c_6450]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_9106,plain,
% 4.08/1.02      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 4.08/1.02      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 4.08/1.02      inference(light_normalisation,[status(thm)],[c_9103,c_8985,c_9035]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_53,negated_conjecture,
% 4.08/1.02      ( v5_pre_topc(sK4,sK2,sK3)
% 4.08/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 4.08/1.02      inference(cnf_transformation,[],[f98]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_95,plain,
% 4.08/1.02      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 4.08/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_49,negated_conjecture,
% 4.08/1.02      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 4.08/1.02      | v5_pre_topc(sK4,sK2,sK3) ),
% 4.08/1.02      inference(cnf_transformation,[],[f102]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_99,plain,
% 4.08/1.02      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
% 4.08/1.02      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_45,negated_conjecture,
% 4.08/1.02      ( v5_pre_topc(sK4,sK2,sK3)
% 4.08/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 4.08/1.02      inference(cnf_transformation,[],[f106]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_103,plain,
% 4.08/1.02      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 4.08/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_37,negated_conjecture,
% 4.08/1.02      ( v5_pre_topc(sK4,sK2,sK3)
% 4.08/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
% 4.08/1.02      inference(cnf_transformation,[],[f114]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_111,plain,
% 4.08/1.02      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 4.08/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_33,negated_conjecture,
% 4.08/1.02      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 4.08/1.02      | v5_pre_topc(sK4,sK2,sK3) ),
% 4.08/1.02      inference(cnf_transformation,[],[f118]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_115,plain,
% 4.08/1.02      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
% 4.08/1.02      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_29,negated_conjecture,
% 4.08/1.02      ( v5_pre_topc(sK4,sK2,sK3)
% 4.08/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 4.08/1.02      inference(cnf_transformation,[],[f122]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_119,plain,
% 4.08/1.02      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 4.08/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3394,plain,
% 4.08/1.02      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 4.08/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 4.08/1.02      | ~ l1_struct_0(sK5)
% 4.08/1.02      | ~ l1_struct_0(sK3)
% 4.08/1.02      | ~ l1_struct_0(sK2)
% 4.08/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 4.08/1.02      | ~ v1_funct_1(sK4) ),
% 4.08/1.02      inference(instantiation,[status(thm)],[c_2391]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3395,plain,
% 4.08/1.02      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | l1_struct_0(sK5) != iProver_top
% 4.08/1.02      | l1_struct_0(sK3) != iProver_top
% 4.08/1.02      | l1_struct_0(sK2) != iProver_top
% 4.08/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top
% 4.08/1.02      | v1_funct_1(sK4) != iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_3394]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_17,plain,
% 4.08/1.02      ( sP0(X0,X1,X2,X3,X4)
% 4.08/1.02      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
% 4.08/1.02      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
% 4.08/1.02      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
% 4.08/1.02      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
% 4.08/1.02      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 4.08/1.02      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
% 4.08/1.02      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
% 4.08/1.02      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
% 4.08/1.02      inference(cnf_transformation,[],[f75]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2390,plain,
% 4.08/1.02      ( sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
% 4.08/1.02      | ~ v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),X1_54,X0_54)
% 4.08/1.02      | ~ v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),X3_54,X0_54)
% 4.08/1.02      | ~ v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),u1_struct_0(X1_54),u1_struct_0(X0_54))
% 4.08/1.02      | ~ v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),u1_struct_0(X3_54),u1_struct_0(X0_54))
% 4.08/1.02      | ~ m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54))))
% 4.08/1.02      | ~ m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X0_54))))
% 4.08/1.02      | ~ v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_55,X1_54))
% 4.08/1.02      | ~ v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_55,X3_54)) ),
% 4.08/1.02      inference(subtyping,[status(esa)],[c_17]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3466,plain,
% 4.08/1.02      ( sP0(X0_54,sK6,X0_55,sK2,sK5)
% 4.08/1.02      | ~ v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK5),sK5,X0_54)
% 4.08/1.02      | ~ v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK6),sK6,X0_54)
% 4.08/1.02      | ~ v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK5),u1_struct_0(sK5),u1_struct_0(X0_54))
% 4.08/1.02      | ~ v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK6),u1_struct_0(sK6),u1_struct_0(X0_54))
% 4.08/1.02      | ~ m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54))))
% 4.08/1.02      | ~ m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_54))))
% 4.08/1.02      | ~ v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK5))
% 4.08/1.02      | ~ v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK6)) ),
% 4.08/1.02      inference(instantiation,[status(thm)],[c_2390]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3467,plain,
% 4.08/1.02      ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK5),sK5,X0_54) != iProver_top
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK6),sK6,X0_54) != iProver_top
% 4.08/1.02      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK5),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 4.08/1.02      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK6),u1_struct_0(sK6),u1_struct_0(X0_54)) != iProver_top
% 4.08/1.02      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 4.08/1.02      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_54)))) != iProver_top
% 4.08/1.02      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK5)) != iProver_top
% 4.08/1.02      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK6)) != iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_3466]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3469,plain,
% 4.08/1.02      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 4.08/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 4.08/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 4.08/1.02      inference(instantiation,[status(thm)],[c_3467]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3502,plain,
% 4.08/1.02      ( ~ l1_pre_topc(sK5) | l1_struct_0(sK5) ),
% 4.08/1.02      inference(instantiation,[status(thm)],[c_2398]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3503,plain,
% 4.08/1.02      ( l1_pre_topc(sK5) != iProver_top
% 4.08/1.02      | l1_struct_0(sK5) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_3502]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_5,plain,
% 4.08/1.02      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 4.08/1.02      inference(cnf_transformation,[],[f55]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2397,plain,
% 4.08/1.02      ( ~ m1_pre_topc(X0_54,X1_54)
% 4.08/1.02      | ~ l1_pre_topc(X1_54)
% 4.08/1.02      | l1_pre_topc(X0_54) ),
% 4.08/1.02      inference(subtyping,[status(esa)],[c_5]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3619,plain,
% 4.08/1.02      ( ~ m1_pre_topc(sK5,X0_54)
% 4.08/1.02      | ~ l1_pre_topc(X0_54)
% 4.08/1.02      | l1_pre_topc(sK5) ),
% 4.08/1.02      inference(instantiation,[status(thm)],[c_2397]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3897,plain,
% 4.08/1.02      ( ~ m1_pre_topc(sK5,sK2) | l1_pre_topc(sK5) | ~ l1_pre_topc(sK2) ),
% 4.08/1.02      inference(instantiation,[status(thm)],[c_3619]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3898,plain,
% 4.08/1.02      ( m1_pre_topc(sK5,sK2) != iProver_top
% 4.08/1.02      | l1_pre_topc(sK5) = iProver_top
% 4.08/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_3897]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2372,negated_conjecture,
% 4.08/1.02      ( m1_pre_topc(sK6,sK2) ),
% 4.08/1.02      inference(subtyping,[status(esa)],[c_62]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3271,plain,
% 4.08/1.02      ( m1_pre_topc(sK6,sK2) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_2372]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3247,plain,
% 4.08/1.02      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 4.08/1.02      | l1_pre_topc(X1_54) != iProver_top
% 4.08/1.02      | l1_pre_topc(X0_54) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_2397]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3968,plain,
% 4.08/1.02      ( l1_pre_topc(sK6) = iProver_top
% 4.08/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_3271,c_3247]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_4978,plain,
% 4.08/1.02      ( l1_pre_topc(sK6) = iProver_top ),
% 4.08/1.02      inference(global_propositional_subsumption,
% 4.08/1.02                [status(thm)],
% 4.08/1.02                [c_3968,c_77]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3246,plain,
% 4.08/1.02      ( l1_pre_topc(X0_54) != iProver_top
% 4.08/1.02      | l1_struct_0(X0_54) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_2398]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_4982,plain,
% 4.08/1.02      ( l1_struct_0(sK6) = iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_4978,c_3246]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_5501,plain,
% 4.08/1.02      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 4.08/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 4.08/1.02      | ~ l1_struct_0(X0_54)
% 4.08/1.02      | ~ l1_struct_0(sK3)
% 4.08/1.02      | ~ l1_struct_0(sK2)
% 4.08/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54))
% 4.08/1.02      | ~ v1_funct_1(sK4) ),
% 4.08/1.02      inference(instantiation,[status(thm)],[c_2391]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_6404,plain,
% 4.08/1.02      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 4.08/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 4.08/1.02      | ~ l1_struct_0(sK6)
% 4.08/1.02      | ~ l1_struct_0(sK3)
% 4.08/1.02      | ~ l1_struct_0(sK2)
% 4.08/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 4.08/1.02      | ~ v1_funct_1(sK4) ),
% 4.08/1.02      inference(instantiation,[status(thm)],[c_5501]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_6405,plain,
% 4.08/1.02      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | l1_struct_0(sK6) != iProver_top
% 4.08/1.02      | l1_struct_0(sK3) != iProver_top
% 4.08/1.02      | l1_struct_0(sK2) != iProver_top
% 4.08/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top
% 4.08/1.02      | v1_funct_1(sK4) != iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_6404]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_9108,plain,
% 4.08/1.02      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 4.08/1.02      inference(global_propositional_subsumption,
% 4.08/1.02                [status(thm)],
% 4.08/1.02                [c_9106,c_77,c_80,c_81,c_82,c_83,c_85,c_95,c_99,c_103,
% 4.08/1.02                 c_111,c_115,c_119,c_180,c_3395,c_3469,c_3503,c_3679,
% 4.08/1.02                 c_3898,c_4982,c_6405]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_8540,plain,
% 4.08/1.02      ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) != iProver_top
% 4.08/1.02      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 4.08/1.02      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 4.08/1.02      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 4.08/1.02      | v2_struct_0(X0_54) = iProver_top
% 4.08/1.02      | v2_pre_topc(X0_54) != iProver_top
% 4.08/1.02      | l1_pre_topc(X0_54) != iProver_top
% 4.08/1.02      | l1_struct_0(X0_54) != iProver_top
% 4.08/1.02      | l1_struct_0(sK2) != iProver_top
% 4.08/1.02      | v1_funct_1(X0_55) != iProver_top
% 4.08/1.02      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) != iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_3251,c_3295]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2447,plain,
% 4.08/1.02      ( l1_pre_topc(X0_54) != iProver_top
% 4.08/1.02      | l1_struct_0(X0_54) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_2398]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_9181,plain,
% 4.08/1.02      ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) != iProver_top
% 4.08/1.02      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 4.08/1.02      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 4.08/1.02      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 4.08/1.02      | v2_struct_0(X0_54) = iProver_top
% 4.08/1.02      | v2_pre_topc(X0_54) != iProver_top
% 4.08/1.02      | l1_pre_topc(X0_54) != iProver_top
% 4.08/1.02      | v1_funct_1(X0_55) != iProver_top
% 4.08/1.02      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) != iProver_top ),
% 4.08/1.02      inference(global_propositional_subsumption,
% 4.08/1.02                [status(thm)],
% 4.08/1.02                [c_8540,c_77,c_2447,c_3679]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_10209,plain,
% 4.08/1.02      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
% 4.08/1.02      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | v2_struct_0(sK3) = iProver_top
% 4.08/1.02      | v2_pre_topc(sK3) != iProver_top
% 4.08/1.02      | l1_pre_topc(sK3) != iProver_top
% 4.08/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
% 4.08/1.02      | v1_funct_1(sK4) != iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_9035,c_9181]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_10219,plain,
% 4.08/1.02      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 4.08/1.02      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 4.08/1.02      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | v2_struct_0(sK3) = iProver_top
% 4.08/1.02      | v2_pre_topc(sK3) != iProver_top
% 4.08/1.02      | l1_pre_topc(sK3) != iProver_top
% 4.08/1.02      | v1_funct_1(sK4) != iProver_top ),
% 4.08/1.02      inference(light_normalisation,[status(thm)],[c_10209,c_9035]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_11032,plain,
% 4.08/1.02      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top ),
% 4.08/1.02      inference(global_propositional_subsumption,
% 4.08/1.02                [status(thm)],
% 4.08/1.02                [c_6938,c_77,c_78,c_79,c_80,c_81,c_82,c_83,c_85,c_95,
% 4.08/1.02                 c_99,c_103,c_111,c_115,c_119,c_180,c_3395,c_3469,c_3503,
% 4.08/1.02                 c_3679,c_3898,c_4982,c_6405,c_9106,c_10219]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_23,plain,
% 4.08/1.02      ( ~ sP0(X0,X1,X2,X3,X4)
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) ),
% 4.08/1.02      inference(cnf_transformation,[],[f69]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2384,plain,
% 4.08/1.02      ( ~ sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),X3_54,X0_54) ),
% 4.08/1.02      inference(subtyping,[status(esa)],[c_23]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3260,plain,
% 4.08/1.02      ( sP0(X0_54,X1_54,X0_55,X2_54,X3_54) != iProver_top
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),X3_54,X0_54) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_2384]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_11040,plain,
% 4.08/1.02      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_11032,c_3260]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2370,negated_conjecture,
% 4.08/1.02      ( m1_pre_topc(sK5,sK2) ),
% 4.08/1.02      inference(subtyping,[status(esa)],[c_64]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3273,plain,
% 4.08/1.02      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_2370]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_6448,plain,
% 4.08/1.02      ( k2_tmap_1(sK2,sK3,sK4,sK5) = k7_relat_1(sK4,u1_struct_0(sK5)) ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_3273,c_6443]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_11047,plain,
% 4.08/1.02      ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) = iProver_top ),
% 4.08/1.02      inference(light_normalisation,[status(thm)],[c_11040,c_6448]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_19,plain,
% 4.08/1.02      ( ~ sP0(X0,X1,X2,X3,X4)
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) ),
% 4.08/1.02      inference(cnf_transformation,[],[f73]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2388,plain,
% 4.08/1.02      ( ~ sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),X1_54,X0_54) ),
% 4.08/1.02      inference(subtyping,[status(esa)],[c_19]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3256,plain,
% 4.08/1.02      ( sP0(X0_54,X1_54,X0_55,X2_54,X3_54) != iProver_top
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),X1_54,X0_54) = iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_2388]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_11041,plain,
% 4.08/1.02      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_11032,c_3256]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_6447,plain,
% 4.08/1.02      ( k2_tmap_1(sK2,sK3,sK4,sK6) = k7_relat_1(sK4,u1_struct_0(sK6)) ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_3271,c_6443]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_11046,plain,
% 4.08/1.02      ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) = iProver_top ),
% 4.08/1.02      inference(light_normalisation,[status(thm)],[c_11041,c_6447]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_27,negated_conjecture,
% 4.08/1.02      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 4.08/1.02      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 4.08/1.02      | ~ v5_pre_topc(sK4,sK2,sK3)
% 4.08/1.02      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 4.08/1.02      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 4.08/1.02      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 4.08/1.02      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 4.08/1.02      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 4.08/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 4.08/1.02      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 4.08/1.02      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 4.08/1.02      | ~ v1_funct_1(sK4) ),
% 4.08/1.02      inference(cnf_transformation,[],[f124]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_484,plain,
% 4.08/1.02      ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 4.08/1.02      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 4.08/1.02      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 4.08/1.02      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 4.08/1.02      | ~ v5_pre_topc(sK4,sK2,sK3)
% 4.08/1.02      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 4.08/1.02      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 4.08/1.02      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 4.08/1.02      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 4.08/1.02      inference(global_propositional_subsumption,
% 4.08/1.02                [status(thm)],
% 4.08/1.02                [c_27,c_68,c_67,c_66]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_485,negated_conjecture,
% 4.08/1.02      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 4.08/1.02      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 4.08/1.02      | ~ v5_pre_topc(sK4,sK2,sK3)
% 4.08/1.02      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 4.08/1.02      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 4.08/1.02      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 4.08/1.02      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 4.08/1.02      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 4.08/1.02      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 4.08/1.02      inference(renaming,[status(thm)],[c_484]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_2359,negated_conjecture,
% 4.08/1.02      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 4.08/1.02      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 4.08/1.02      | ~ v5_pre_topc(sK4,sK2,sK3)
% 4.08/1.02      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 4.08/1.02      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 4.08/1.02      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 4.08/1.02      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 4.08/1.02      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 4.08/1.02      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 4.08/1.02      inference(subtyping,[status(esa)],[c_485]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_3284,plain,
% 4.08/1.02      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 4.08/1.02      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 4.08/1.02      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 4.08/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 4.08/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 4.08/1.02      inference(predicate_to_equality,[status(thm)],[c_2359]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_6459,plain,
% 4.08/1.02      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 4.08/1.02      | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) != iProver_top
% 4.08/1.02      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 4.08/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 4.08/1.02      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) != iProver_top ),
% 4.08/1.02      inference(demodulation,[status(thm)],[c_6447,c_3284]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_6460,plain,
% 4.08/1.02      ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) != iProver_top
% 4.08/1.02      | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) != iProver_top
% 4.08/1.02      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 4.08/1.02      | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK5))) != iProver_top
% 4.08/1.02      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) != iProver_top ),
% 4.08/1.02      inference(light_normalisation,[status(thm)],[c_6459,c_6448]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_8533,plain,
% 4.08/1.02      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top
% 4.08/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | l1_struct_0(sK6) != iProver_top
% 4.08/1.02      | l1_struct_0(sK3) != iProver_top
% 4.08/1.02      | l1_struct_0(sK2) != iProver_top
% 4.08/1.02      | v1_funct_1(sK4) != iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_6447,c_3251]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_8534,plain,
% 4.08/1.02      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top
% 4.08/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | l1_struct_0(sK5) != iProver_top
% 4.08/1.02      | l1_struct_0(sK3) != iProver_top
% 4.08/1.02      | l1_struct_0(sK2) != iProver_top
% 4.08/1.02      | v1_funct_1(sK4) != iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_6448,c_3251]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_8664,plain,
% 4.08/1.02      ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top
% 4.08/1.02      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | l1_struct_0(sK6) != iProver_top
% 4.08/1.02      | l1_struct_0(sK3) != iProver_top
% 4.08/1.02      | l1_struct_0(sK2) != iProver_top
% 4.08/1.02      | v1_funct_1(sK4) != iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_6447,c_3252]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_8665,plain,
% 4.08/1.02      ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
% 4.08/1.02      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 4.08/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.02      | l1_struct_0(sK5) != iProver_top
% 4.08/1.02      | l1_struct_0(sK3) != iProver_top
% 4.08/1.02      | l1_struct_0(sK2) != iProver_top
% 4.08/1.02      | v1_funct_1(sK4) != iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_6448,c_3252]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_8790,plain,
% 4.08/1.02      ( l1_struct_0(sK6) != iProver_top
% 4.08/1.02      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) = iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_6447,c_8785]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_8791,plain,
% 4.08/1.02      ( l1_struct_0(sK5) != iProver_top
% 4.08/1.02      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK5))) = iProver_top ),
% 4.08/1.02      inference(superposition,[status(thm)],[c_6448,c_8785]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_10312,plain,
% 4.08/1.02      ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) != iProver_top
% 4.08/1.02      | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) != iProver_top ),
% 4.08/1.02      inference(global_propositional_subsumption,
% 4.08/1.02                [status(thm)],
% 4.08/1.02                [c_6460,c_77,c_80,c_81,c_82,c_83,c_85,c_95,c_99,c_103,
% 4.08/1.02                 c_111,c_115,c_119,c_180,c_3395,c_3469,c_3503,c_3679,
% 4.08/1.02                 c_3898,c_4982,c_6405,c_8533,c_8534,c_8664,c_8665,c_8790,
% 4.08/1.02                 c_8791,c_9106]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(c_10313,plain,
% 4.08/1.02      ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) != iProver_top
% 4.08/1.02      | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) != iProver_top ),
% 4.08/1.02      inference(renaming,[status(thm)],[c_10312]) ).
% 4.08/1.02  
% 4.08/1.02  cnf(contradiction,plain,
% 4.08/1.02      ( $false ),
% 4.08/1.02      inference(minisat,[status(thm)],[c_11047,c_11046,c_10313]) ).
% 4.08/1.02  
% 4.08/1.02  
% 4.08/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 4.08/1.02  
% 4.08/1.02  ------                               Statistics
% 4.08/1.02  
% 4.08/1.02  ------ General
% 4.08/1.02  
% 4.08/1.02  abstr_ref_over_cycles:                  0
% 4.08/1.02  abstr_ref_under_cycles:                 0
% 4.08/1.02  gc_basic_clause_elim:                   0
% 4.08/1.02  forced_gc_time:                         0
% 4.08/1.02  parsing_time:                           0.041
% 4.08/1.02  unif_index_cands_time:                  0.
% 4.08/1.02  unif_index_add_time:                    0.
% 4.08/1.02  orderings_time:                         0.
% 4.08/1.02  out_proof_time:                         0.024
% 4.08/1.02  total_time:                             0.478
% 4.08/1.02  num_of_symbols:                         59
% 4.08/1.02  num_of_terms:                           11143
% 4.08/1.02  
% 4.08/1.02  ------ Preprocessing
% 4.08/1.02  
% 4.08/1.02  num_of_splits:                          0
% 4.08/1.02  num_of_split_atoms:                     0
% 4.08/1.02  num_of_reused_defs:                     0
% 4.08/1.02  num_eq_ax_congr_red:                    29
% 4.08/1.02  num_of_sem_filtered_clauses:            1
% 4.08/1.02  num_of_subtypes:                        5
% 4.08/1.02  monotx_restored_types:                  0
% 4.08/1.02  sat_num_of_epr_types:                   0
% 4.08/1.02  sat_num_of_non_cyclic_types:            0
% 4.08/1.02  sat_guarded_non_collapsed_types:        1
% 4.08/1.02  num_pure_diseq_elim:                    0
% 4.08/1.02  simp_replaced_by:                       0
% 4.08/1.02  res_preprocessed:                       237
% 4.08/1.02  prep_upred:                             0
% 4.08/1.02  prep_unflattend:                        148
% 4.08/1.02  smt_new_axioms:                         0
% 4.08/1.02  pred_elim_cands:                        10
% 4.08/1.02  pred_elim:                              4
% 4.08/1.02  pred_elim_cl:                           4
% 4.08/1.02  pred_elim_cycles:                       6
% 4.08/1.02  merged_defs:                            0
% 4.08/1.02  merged_defs_ncl:                        0
% 4.08/1.02  bin_hyper_res:                          0
% 4.08/1.02  prep_cycles:                            4
% 4.08/1.02  pred_elim_time:                         0.04
% 4.08/1.02  splitting_time:                         0.
% 4.08/1.02  sem_filter_time:                        0.
% 4.08/1.02  monotx_time:                            0.
% 4.08/1.02  subtype_inf_time:                       0.
% 4.08/1.02  
% 4.08/1.02  ------ Problem properties
% 4.08/1.02  
% 4.08/1.02  clauses:                                47
% 4.08/1.02  conjectures:                            23
% 4.08/1.02  epr:                                    13
% 4.08/1.02  horn:                                   31
% 4.08/1.02  ground:                                 23
% 4.08/1.02  unary:                                  14
% 4.08/1.02  binary:                                 18
% 4.08/1.02  lits:                                   163
% 4.08/1.02  lits_eq:                                4
% 4.08/1.02  fd_pure:                                0
% 4.08/1.02  fd_pseudo:                              0
% 4.08/1.02  fd_cond:                                0
% 4.08/1.02  fd_pseudo_cond:                         0
% 4.08/1.02  ac_symbols:                             0
% 4.08/1.02  
% 4.08/1.02  ------ Propositional Solver
% 4.08/1.02  
% 4.08/1.02  prop_solver_calls:                      30
% 4.08/1.02  prop_fast_solver_calls:                 2934
% 4.08/1.02  smt_solver_calls:                       0
% 4.08/1.02  smt_fast_solver_calls:                  0
% 4.08/1.02  prop_num_of_clauses:                    4104
% 4.08/1.02  prop_preprocess_simplified:             12048
% 4.08/1.02  prop_fo_subsumed:                       240
% 4.08/1.02  prop_solver_time:                       0.
% 4.08/1.02  smt_solver_time:                        0.
% 4.08/1.02  smt_fast_solver_time:                   0.
% 4.08/1.02  prop_fast_solver_time:                  0.
% 4.08/1.02  prop_unsat_core_time:                   0.
% 4.08/1.02  
% 4.08/1.02  ------ QBF
% 4.08/1.02  
% 4.08/1.02  qbf_q_res:                              0
% 4.08/1.02  qbf_num_tautologies:                    0
% 4.08/1.02  qbf_prep_cycles:                        0
% 4.08/1.02  
% 4.08/1.02  ------ BMC1
% 4.08/1.02  
% 4.08/1.02  bmc1_current_bound:                     -1
% 4.08/1.02  bmc1_last_solved_bound:                 -1
% 4.08/1.02  bmc1_unsat_core_size:                   -1
% 4.08/1.02  bmc1_unsat_core_parents_size:           -1
% 4.08/1.02  bmc1_merge_next_fun:                    0
% 4.08/1.02  bmc1_unsat_core_clauses_time:           0.
% 4.08/1.02  
% 4.08/1.02  ------ Instantiation
% 4.08/1.02  
% 4.08/1.02  inst_num_of_clauses:                    1195
% 4.08/1.02  inst_num_in_passive:                    392
% 4.08/1.02  inst_num_in_active:                     633
% 4.08/1.02  inst_num_in_unprocessed:                170
% 4.08/1.02  inst_num_of_loops:                      680
% 4.08/1.02  inst_num_of_learning_restarts:          0
% 4.08/1.02  inst_num_moves_active_passive:          44
% 4.08/1.02  inst_lit_activity:                      0
% 4.08/1.02  inst_lit_activity_moves:                1
% 4.08/1.02  inst_num_tautologies:                   0
% 4.08/1.02  inst_num_prop_implied:                  0
% 4.08/1.02  inst_num_existing_simplified:           0
% 4.08/1.02  inst_num_eq_res_simplified:             0
% 4.08/1.02  inst_num_child_elim:                    0
% 4.08/1.02  inst_num_of_dismatching_blockings:      1020
% 4.08/1.02  inst_num_of_non_proper_insts:           1131
% 4.08/1.02  inst_num_of_duplicates:                 0
% 4.08/1.02  inst_inst_num_from_inst_to_res:         0
% 4.08/1.02  inst_dismatching_checking_time:         0.
% 4.08/1.02  
% 4.08/1.02  ------ Resolution
% 4.08/1.02  
% 4.08/1.02  res_num_of_clauses:                     0
% 4.08/1.02  res_num_in_passive:                     0
% 4.08/1.02  res_num_in_active:                      0
% 4.08/1.02  res_num_of_loops:                       241
% 4.08/1.02  res_forward_subset_subsumed:            88
% 4.08/1.02  res_backward_subset_subsumed:           0
% 4.08/1.02  res_forward_subsumed:                   0
% 4.08/1.02  res_backward_subsumed:                  0
% 4.08/1.02  res_forward_subsumption_resolution:     0
% 4.08/1.02  res_backward_subsumption_resolution:    0
% 4.08/1.02  res_clause_to_clause_subsumption:       708
% 4.08/1.02  res_orphan_elimination:                 0
% 4.08/1.02  res_tautology_del:                      81
% 4.08/1.02  res_num_eq_res_simplified:              0
% 4.08/1.02  res_num_sel_changes:                    0
% 4.08/1.02  res_moves_from_active_to_pass:          0
% 4.08/1.02  
% 4.08/1.02  ------ Superposition
% 4.08/1.02  
% 4.08/1.02  sup_time_total:                         0.
% 4.08/1.02  sup_time_generating:                    0.
% 4.08/1.02  sup_time_sim_full:                      0.
% 4.08/1.02  sup_time_sim_immed:                     0.
% 4.08/1.02  
% 4.08/1.02  sup_num_of_clauses:                     229
% 4.08/1.02  sup_num_in_active:                      114
% 4.08/1.02  sup_num_in_passive:                     115
% 4.08/1.02  sup_num_of_loops:                       135
% 4.08/1.02  sup_fw_superposition:                   116
% 4.08/1.02  sup_bw_superposition:                   128
% 4.08/1.02  sup_immediate_simplified:               77
% 4.08/1.02  sup_given_eliminated:                   0
% 4.08/1.02  comparisons_done:                       0
% 4.08/1.02  comparisons_avoided:                    0
% 4.08/1.02  
% 4.08/1.02  ------ Simplifications
% 4.08/1.02  
% 4.08/1.02  
% 4.08/1.02  sim_fw_subset_subsumed:                 6
% 4.08/1.02  sim_bw_subset_subsumed:                 8
% 4.08/1.02  sim_fw_subsumed:                        6
% 4.08/1.02  sim_bw_subsumed:                        4
% 4.08/1.02  sim_fw_subsumption_res:                 0
% 4.08/1.02  sim_bw_subsumption_res:                 0
% 4.08/1.02  sim_tautology_del:                      10
% 4.08/1.02  sim_eq_tautology_del:                   10
% 4.08/1.02  sim_eq_res_simp:                        0
% 4.08/1.02  sim_fw_demodulated:                     3
% 4.08/1.02  sim_bw_demodulated:                     18
% 4.08/1.02  sim_light_normalised:                   79
% 4.08/1.02  sim_joinable_taut:                      0
% 4.08/1.02  sim_joinable_simp:                      0
% 4.08/1.02  sim_ac_normalised:                      0
% 4.08/1.02  sim_smt_subsumption:                    0
% 4.08/1.02  
%------------------------------------------------------------------------------
