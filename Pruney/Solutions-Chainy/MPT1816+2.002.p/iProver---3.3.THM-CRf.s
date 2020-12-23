%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:18 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  296 (16858 expanded)
%              Number of clauses        :  203 (3696 expanded)
%              Number of leaves         :   22 (5910 expanded)
%              Depth                    :   27
%              Number of atoms          : 1912 (530584 expanded)
%              Number of equality atoms :  485 (20988 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   78 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f52,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f46,f51,f50,f49,f48,f47])).

fof(f95,plain,(
    k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f52])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f82,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f91,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f92,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f93,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f94,plain,(
    m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f90,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f52])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f83,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f89,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
      <=> sP0(X1,X3,X4,X0,X2) )
      | ~ sP1(X2,X0,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0)
      | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
      | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
      | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f41])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f35,plain,(
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

fof(f37,plain,(
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
    inference(definition_folding,[],[f32,f36,f35])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f96,plain,(
    r4_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f103,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f107,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f111,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f119,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f123,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f127,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f129,plain,
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
    inference(cnf_transformation,[],[f52])).

cnf(c_63,negated_conjecture,
    ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2417,negated_conjecture,
    ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(subtyping,[status(esa)],[c_63])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2439,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_pre_topc(X2_56,X1_56)
    | m1_pre_topc(k1_tsep_1(X1_56,X0_56,X2_56),X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X2_56)
    | ~ l1_pre_topc(X1_56) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_3293,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | m1_pre_topc(X2_56,X1_56) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1_56,X0_56,X2_56),X1_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | l1_pre_topc(X1_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2439])).

cnf(c_5511,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2417,c_3293])).

cnf(c_76,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_77,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_76])).

cnf(c_74,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_79,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_74])).

cnf(c_67,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_86,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_67])).

cnf(c_66,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_87,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66])).

cnf(c_65,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_88,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65])).

cnf(c_64,negated_conjecture,
    ( m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_89,plain,
    ( m1_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64])).

cnf(c_3474,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | m1_pre_topc(k1_tsep_1(X1_56,sK5,X0_56),X1_56)
    | ~ m1_pre_topc(sK5,X1_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(X1_56) ),
    inference(instantiation,[status(thm)],[c_2439])).

cnf(c_3623,plain,
    ( ~ m1_pre_topc(X0_56,sK2)
    | m1_pre_topc(k1_tsep_1(sK2,sK5,X0_56),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(X0_56)
    | v2_struct_0(sK5)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3474])).

cnf(c_3892,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3623])).

cnf(c_3893,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3892])).

cnf(c_2445,plain,
    ( X0_56 = X0_56 ),
    theory(equality)).

cnf(c_3957,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_2445])).

cnf(c_2450,plain,
    ( X0_56 != X1_56
    | X2_56 != X1_56
    | X2_56 = X0_56 ),
    theory(equality)).

cnf(c_3803,plain,
    ( X0_56 != X1_56
    | sK2 != X1_56
    | sK2 = X0_56 ),
    inference(instantiation,[status(thm)],[c_2450])).

cnf(c_3959,plain,
    ( X0_56 != sK2
    | sK2 = X0_56
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3803])).

cnf(c_4391,plain,
    ( k1_tsep_1(sK2,sK5,sK6) != sK2
    | sK2 = k1_tsep_1(sK2,sK5,sK6)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3959])).

cnf(c_2458,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | m1_pre_topc(X2_56,X3_56)
    | X2_56 != X0_56
    | X3_56 != X1_56 ),
    theory(equality)).

cnf(c_3645,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | m1_pre_topc(X2_56,sK2)
    | X2_56 != X0_56
    | sK2 != X1_56 ),
    inference(instantiation,[status(thm)],[c_2458])).

cnf(c_3834,plain,
    ( ~ m1_pre_topc(X0_56,sK2)
    | m1_pre_topc(X1_56,sK2)
    | X1_56 != X0_56
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3645])).

cnf(c_4323,plain,
    ( m1_pre_topc(X0_56,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2)
    | X0_56 != k1_tsep_1(sK2,sK5,sK6)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3834])).

cnf(c_5051,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2)
    | m1_pre_topc(sK2,sK2)
    | sK2 != k1_tsep_1(sK2,sK5,sK6)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4323])).

cnf(c_5052,plain,
    ( sK2 != k1_tsep_1(sK2,sK5,sK6)
    | sK2 != sK2
    | m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5051])).

cnf(c_6266,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5511,c_77,c_79,c_86,c_87,c_88,c_89,c_2417,c_3893,c_3957,c_4391,c_5052])).

cnf(c_68,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2412,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_68])).

cnf(c_3319,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2412])).

cnf(c_8,plain,
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
    inference(cnf_transformation,[],[f61])).

cnf(c_2440,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_pre_topc(X2_56,X0_56)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | ~ v2_pre_topc(X0_56)
    | ~ v2_pre_topc(X1_56)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(X1_56)
    | ~ v1_funct_1(X0_57)
    | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_57,u1_struct_0(X2_56)) = k2_tmap_1(X0_56,X1_56,X0_57,X2_56) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_3292,plain,
    ( k2_partfun1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_57,u1_struct_0(X2_56)) = k2_tmap_1(X0_56,X1_56,X0_57,X2_56)
    | v1_funct_2(X0_57,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v1_funct_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2440])).

cnf(c_4586,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_56)) = k2_tmap_1(sK2,sK3,sK4,X0_56)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_56,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3319,c_3292])).

cnf(c_75,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_78,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_75])).

cnf(c_73,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_80,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_72,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_81,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_72])).

cnf(c_71,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_82,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_70,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_83,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_70])).

cnf(c_69,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_84,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_6481,plain,
    ( m1_pre_topc(X0_56,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_56)) = k2_tmap_1(sK2,sK3,sK4,X0_56) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4586,c_77,c_78,c_79,c_80,c_81,c_82,c_83,c_84])).

cnf(c_6482,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_56)) = k2_tmap_1(sK2,sK3,sK4,X0_56)
    | m1_pre_topc(X0_56,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6481])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2443,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
    | ~ v1_funct_1(X0_57)
    | k2_partfun1(X0_58,X1_58,X0_57,X2_58) = k7_relat_1(X0_57,X2_58) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3289,plain,
    ( k2_partfun1(X0_58,X1_58,X0_57,X2_58) = k7_relat_1(X0_57,X2_58)
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2443])).

cnf(c_3874,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_58) = k7_relat_1(sK4,X0_58)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3319,c_3289])).

cnf(c_5142,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_58) = k7_relat_1(sK4,X0_58) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3874,c_83])).

cnf(c_6487,plain,
    ( k2_tmap_1(sK2,sK3,sK4,X0_56) = k7_relat_1(sK4,u1_struct_0(X0_56))
    | m1_pre_topc(X0_56,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6482,c_5142])).

cnf(c_6494,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_6266,c_6487])).

cnf(c_18,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | sP0(X4,X3,X2,X1,X0)
    | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
    | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
    | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
    | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_28,plain,
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
    inference(cnf_transformation,[],[f81])).

cnf(c_62,negated_conjecture,
    ( r4_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_816,plain,
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
    inference(resolution_lifted,[status(thm)],[c_28,c_62])).

cnf(c_817,plain,
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
    inference(unflattening,[status(thm)],[c_816])).

cnf(c_821,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | sP1(sK5,sK2,X0,sK6,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_817,c_76,c_75,c_74,c_67,c_66,c_65,c_64])).

cnf(c_822,plain,
    ( sP1(sK5,sK2,X0,sK6,X1)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_821])).

cnf(c_857,plain,
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
    inference(resolution_lifted,[status(thm)],[c_18,c_822])).

cnf(c_858,plain,
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
    inference(unflattening,[status(thm)],[c_857])).

cnf(c_2401,plain,
    ( sP0(X0_56,sK6,X0_57,sK2,sK5)
    | ~ v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_56)
    | ~ v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56))
    | ~ v1_funct_2(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_56))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56))))
    | ~ m1_subset_1(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_56))))
    | v2_struct_0(X0_56)
    | ~ v2_pre_topc(X0_56)
    | ~ l1_pre_topc(X0_56)
    | ~ v1_funct_1(X0_57)
    | ~ v1_funct_1(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(subtyping,[status(esa)],[c_858])).

cnf(c_3330,plain,
    ( sP0(X0_56,sK6,X0_57,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_56) != iProver_top
    | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_56)))) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2401])).

cnf(c_3339,plain,
    ( sP0(X0_56,sK6,X0_57,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,sK2),sK2,X0_56) != iProver_top
    | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_56,X0_57,sK2),u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_56,X0_57,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56)))) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_56,X0_57,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3330,c_2417])).

cnf(c_6979,plain,
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
    inference(superposition,[status(thm)],[c_6494,c_3339])).

cnf(c_6982,plain,
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
    inference(light_normalisation,[status(thm)],[c_6979,c_6494])).

cnf(c_85,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_68])).

cnf(c_14,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_986,plain,
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
    inference(resolution_lifted,[status(thm)],[c_14,c_822])).

cnf(c_987,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_986])).

cnf(c_2397,plain,
    ( ~ sP0(X0_56,sK6,X0_57,sK2,sK5)
    | ~ v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56))))
    | m1_subset_1(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_56))))
    | v2_struct_0(X0_56)
    | ~ v2_pre_topc(X0_56)
    | ~ l1_pre_topc(X0_56)
    | ~ v1_funct_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_987])).

cnf(c_3334,plain,
    ( sP0(X0_56,sK6,X0_57,sK2,sK5) != iProver_top
    | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_56)))) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v1_funct_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2397])).

cnf(c_3338,plain,
    ( sP0(X0_56,sK6,X0_57,sK2,sK5) != iProver_top
    | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_56,X0_57,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56)))) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v1_funct_1(X0_57) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3334,c_2417])).

cnf(c_6980,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6494,c_3338])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_180,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_182,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_180])).

cnf(c_2442,plain,
    ( ~ l1_pre_topc(X0_56)
    | l1_struct_0(X0_56) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3722,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2442])).

cnf(c_3723,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3722])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2437,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | m1_subset_1(k2_tmap_1(X0_56,X1_56,X0_57,X2_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
    | ~ l1_struct_0(X2_56)
    | ~ l1_struct_0(X1_56)
    | ~ l1_struct_0(X0_56)
    | ~ v1_funct_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_3295,plain,
    ( v1_funct_2(X0_57,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_56,X1_56,X0_57,X2_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56)))) = iProver_top
    | l1_struct_0(X2_56) != iProver_top
    | l1_struct_0(X1_56) != iProver_top
    | l1_struct_0(X0_56) != iProver_top
    | v1_funct_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2437])).

cnf(c_8579,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6494,c_3295])).

cnf(c_8973,plain,
    ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6980,c_79,c_82,c_83,c_84,c_85,c_182,c_3723,c_8579])).

cnf(c_15,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_956,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_822])).

cnf(c_957,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_956])).

cnf(c_2398,plain,
    ( ~ sP0(X0_56,sK6,X0_57,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_56)
    | ~ v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56))))
    | v2_struct_0(X0_56)
    | ~ v2_pre_topc(X0_56)
    | ~ l1_pre_topc(X0_56)
    | ~ v1_funct_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_957])).

cnf(c_3333,plain,
    ( sP0(X0_56,sK6,X0_57,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_56) = iProver_top
    | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56)))) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v1_funct_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2398])).

cnf(c_3336,plain,
    ( sP0(X0_56,sK6,X0_57,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,sK2),sK2,X0_56) = iProver_top
    | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56)))) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v1_funct_1(X0_57) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3333,c_2417])).

cnf(c_8977,plain,
    ( sP0(sK3,sK6,k7_relat_1(sK4,u1_struct_0(sK2)),sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,k7_relat_1(sK4,u1_struct_0(sK2)),sK2),sK2,sK3) = iProver_top
    | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8973,c_3336])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2436,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | v1_funct_2(k2_tmap_1(X0_56,X1_56,X0_57,X2_56),u1_struct_0(X2_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ l1_struct_0(X2_56)
    | ~ l1_struct_0(X1_56)
    | ~ l1_struct_0(X0_56)
    | ~ v1_funct_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3296,plain,
    ( v1_funct_2(X0_57,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_56,X1_56,X0_57,X2_56),u1_struct_0(X2_56),u1_struct_0(X1_56)) = iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | l1_struct_0(X2_56) != iProver_top
    | l1_struct_0(X1_56) != iProver_top
    | l1_struct_0(X0_56) != iProver_top
    | v1_funct_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2436])).

cnf(c_8710,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6494,c_3296])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2435,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ l1_struct_0(X2_56)
    | ~ l1_struct_0(X1_56)
    | ~ l1_struct_0(X0_56)
    | ~ v1_funct_1(X0_57)
    | v1_funct_1(k2_tmap_1(X0_56,X1_56,X0_57,X2_56)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_3297,plain,
    ( v1_funct_2(X0_57,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | l1_struct_0(X2_56) != iProver_top
    | l1_struct_0(X1_56) != iProver_top
    | l1_struct_0(X0_56) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_56,X1_56,X0_57,X2_56)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2435])).

cnf(c_8604,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | l1_struct_0(X0_56) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_56)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3319,c_3297])).

cnf(c_8828,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_56)) = iProver_top
    | l1_struct_0(X0_56) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8604,c_79,c_82,c_83,c_84,c_182,c_3723])).

cnf(c_8829,plain,
    ( l1_struct_0(X0_56) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_56)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8828])).

cnf(c_8836,plain,
    ( l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6494,c_8829])).

cnf(c_9146,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,k7_relat_1(sK4,u1_struct_0(sK2)),sK2),sK2,sK3) = iProver_top
    | sP0(sK3,sK6,k7_relat_1(sK4,u1_struct_0(sK2)),sK2,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8977,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_182,c_3723,c_8710,c_8836])).

cnf(c_9147,plain,
    ( sP0(sK3,sK6,k7_relat_1(sK4,u1_struct_0(sK2)),sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,k7_relat_1(sK4,u1_struct_0(sK2)),sK2),sK2,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_9146])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_775,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_4,c_1])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_779,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_775,c_3])).

cnf(c_780,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_779])).

cnf(c_2,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_796,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_780,c_2])).

cnf(c_800,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_796,c_3])).

cnf(c_2402,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
    | k7_relat_1(X0_57,X0_58) = X0_57 ),
    inference(subtyping,[status(esa)],[c_800])).

cnf(c_3329,plain,
    ( k7_relat_1(X0_57,X0_58) = X0_57
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2402])).

cnf(c_9029,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK4 ),
    inference(superposition,[status(thm)],[c_3319,c_3329])).

cnf(c_9079,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4 ),
    inference(demodulation,[status(thm)],[c_9029,c_6494])).

cnf(c_9150,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9147,c_9029,c_9079])).

cnf(c_55,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_97,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_51,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_101,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_47,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_105,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_39,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_113,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_35,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_117,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_31,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_121,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3438,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2435])).

cnf(c_3439,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3438])).

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
    inference(cnf_transformation,[],[f80])).

cnf(c_2434,plain,
    ( sP0(X0_56,X1_56,X0_57,X2_56,X3_56)
    | ~ v5_pre_topc(k2_tmap_1(X2_56,X0_56,X0_57,X1_56),X1_56,X0_56)
    | ~ v5_pre_topc(k2_tmap_1(X2_56,X0_56,X0_57,X3_56),X3_56,X0_56)
    | ~ v1_funct_2(k2_tmap_1(X2_56,X0_56,X0_57,X1_56),u1_struct_0(X1_56),u1_struct_0(X0_56))
    | ~ v1_funct_2(k2_tmap_1(X2_56,X0_56,X0_57,X3_56),u1_struct_0(X3_56),u1_struct_0(X0_56))
    | ~ m1_subset_1(k2_tmap_1(X2_56,X0_56,X0_57,X1_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(X0_56))))
    | ~ m1_subset_1(k2_tmap_1(X2_56,X0_56,X0_57,X3_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_56),u1_struct_0(X0_56))))
    | ~ v1_funct_1(k2_tmap_1(X2_56,X0_56,X0_57,X1_56))
    | ~ v1_funct_1(k2_tmap_1(X2_56,X0_56,X0_57,X3_56)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_3510,plain,
    ( sP0(X0_56,sK6,X0_57,sK2,sK5)
    | ~ v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,sK5),sK5,X0_56)
    | ~ v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,sK6),sK6,X0_56)
    | ~ v1_funct_2(k2_tmap_1(sK2,X0_56,X0_57,sK5),u1_struct_0(sK5),u1_struct_0(X0_56))
    | ~ v1_funct_2(k2_tmap_1(sK2,X0_56,X0_57,sK6),u1_struct_0(sK6),u1_struct_0(X0_56))
    | ~ m1_subset_1(k2_tmap_1(sK2,X0_56,X0_57,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_56))))
    | ~ m1_subset_1(k2_tmap_1(sK2,X0_56,X0_57,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_56))))
    | ~ v1_funct_1(k2_tmap_1(sK2,X0_56,X0_57,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,X0_56,X0_57,sK6)) ),
    inference(instantiation,[status(thm)],[c_2434])).

cnf(c_3511,plain,
    ( sP0(X0_56,sK6,X0_57,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,sK5),sK5,X0_56) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,sK6),sK6,X0_56) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_56,X0_57,sK5),u1_struct_0(sK5),u1_struct_0(X0_56)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_56,X0_57,sK6),u1_struct_0(sK6),u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_56,X0_57,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_56)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_56,X0_57,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_56)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_56,X0_57,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_56,X0_57,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3510])).

cnf(c_3513,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3511])).

cnf(c_3546,plain,
    ( ~ l1_pre_topc(sK5)
    | l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2442])).

cnf(c_3547,plain,
    ( l1_pre_topc(sK5) != iProver_top
    | l1_struct_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3546])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2441,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ l1_pre_topc(X1_56)
    | l1_pre_topc(X0_56) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3663,plain,
    ( ~ m1_pre_topc(sK5,X0_56)
    | ~ l1_pre_topc(X0_56)
    | l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_2441])).

cnf(c_3941,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3663])).

cnf(c_3942,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | l1_pre_topc(sK5) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3941])).

cnf(c_2416,negated_conjecture,
    ( m1_pre_topc(sK6,sK2) ),
    inference(subtyping,[status(esa)],[c_64])).

cnf(c_3315,plain,
    ( m1_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2416])).

cnf(c_3291,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2441])).

cnf(c_4012,plain,
    ( l1_pre_topc(sK6) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3315,c_3291])).

cnf(c_5022,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4012,c_79])).

cnf(c_3290,plain,
    ( l1_pre_topc(X0_56) != iProver_top
    | l1_struct_0(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2442])).

cnf(c_5026,plain,
    ( l1_struct_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_5022,c_3290])).

cnf(c_5545,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(X0_56)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_56))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2435])).

cnf(c_6448,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK6)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5545])).

cnf(c_6449,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6448])).

cnf(c_9152,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9150,c_79,c_82,c_83,c_84,c_85,c_87,c_97,c_101,c_105,c_113,c_117,c_121,c_182,c_3439,c_3513,c_3547,c_3723,c_3942,c_5026,c_6449])).

cnf(c_8584,plain,
    ( sP0(X0_56,sK6,X0_57,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,sK2),sK2,X0_56) != iProver_top
    | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_56,X0_57,sK2),u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56)))) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_struct_0(X0_56) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_56,X0_57,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3295,c_3339])).

cnf(c_2491,plain,
    ( l1_pre_topc(X0_56) != iProver_top
    | l1_struct_0(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2442])).

cnf(c_9225,plain,
    ( sP0(X0_56,sK6,X0_57,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,sK2),sK2,X0_56) != iProver_top
    | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_56,X0_57,sK2),u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56)))) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_56,X0_57,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8584,c_79,c_2491,c_3723])).

cnf(c_10253,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9079,c_9225])).

cnf(c_10263,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10253,c_9079])).

cnf(c_11076,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6982,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_87,c_97,c_101,c_105,c_113,c_117,c_121,c_182,c_3439,c_3513,c_3547,c_3723,c_3942,c_5026,c_6449,c_9150,c_10263])).

cnf(c_25,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2428,plain,
    ( ~ sP0(X0_56,X1_56,X0_57,X2_56,X3_56)
    | v5_pre_topc(k2_tmap_1(X2_56,X0_56,X0_57,X3_56),X3_56,X0_56) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_3304,plain,
    ( sP0(X0_56,X1_56,X0_57,X2_56,X3_56) != iProver_top
    | v5_pre_topc(k2_tmap_1(X2_56,X0_56,X0_57,X3_56),X3_56,X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2428])).

cnf(c_11084,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_11076,c_3304])).

cnf(c_2414,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(subtyping,[status(esa)],[c_66])).

cnf(c_3317,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2414])).

cnf(c_6492,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK5) = k7_relat_1(sK4,u1_struct_0(sK5)) ),
    inference(superposition,[status(thm)],[c_3317,c_6487])).

cnf(c_11091,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11084,c_6492])).

cnf(c_21,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2432,plain,
    ( ~ sP0(X0_56,X1_56,X0_57,X2_56,X3_56)
    | v5_pre_topc(k2_tmap_1(X2_56,X0_56,X0_57,X1_56),X1_56,X0_56) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_3300,plain,
    ( sP0(X0_56,X1_56,X0_57,X2_56,X3_56) != iProver_top
    | v5_pre_topc(k2_tmap_1(X2_56,X0_56,X0_57,X1_56),X1_56,X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2432])).

cnf(c_11085,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_11076,c_3300])).

cnf(c_6491,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK6) = k7_relat_1(sK4,u1_struct_0(sK6)) ),
    inference(superposition,[status(thm)],[c_3315,c_6487])).

cnf(c_11090,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11085,c_6491])).

cnf(c_29,negated_conjecture,
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
    inference(cnf_transformation,[],[f129])).

cnf(c_496,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29,c_70,c_69,c_68])).

cnf(c_497,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(renaming,[status(thm)],[c_496])).

cnf(c_2403,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(subtyping,[status(esa)],[c_497])).

cnf(c_3328,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2403])).

cnf(c_6503,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6491,c_3328])).

cnf(c_6504,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) != iProver_top
    | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK5))) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6503,c_6492])).

cnf(c_8577,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6491,c_3295])).

cnf(c_8578,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6492,c_3295])).

cnf(c_8708,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6491,c_3296])).

cnf(c_8709,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6492,c_3296])).

cnf(c_8834,plain,
    ( l1_struct_0(sK6) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6491,c_8829])).

cnf(c_8835,plain,
    ( l1_struct_0(sK5) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6492,c_8829])).

cnf(c_10356,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) != iProver_top
    | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6504,c_79,c_82,c_83,c_84,c_85,c_87,c_97,c_101,c_105,c_113,c_117,c_121,c_182,c_3439,c_3513,c_3547,c_3723,c_3942,c_5026,c_6449,c_8577,c_8578,c_8708,c_8709,c_8834,c_8835,c_9150])).

cnf(c_10357,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) != iProver_top
    | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_10356])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11091,c_11090,c_10357])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:28:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.88/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.01  
% 3.88/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.88/1.01  
% 3.88/1.01  ------  iProver source info
% 3.88/1.01  
% 3.88/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.88/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.88/1.01  git: non_committed_changes: false
% 3.88/1.01  git: last_make_outside_of_git: false
% 3.88/1.01  
% 3.88/1.01  ------ 
% 3.88/1.01  
% 3.88/1.01  ------ Input Options
% 3.88/1.01  
% 3.88/1.01  --out_options                           all
% 3.88/1.01  --tptp_safe_out                         true
% 3.88/1.01  --problem_path                          ""
% 3.88/1.01  --include_path                          ""
% 3.88/1.01  --clausifier                            res/vclausify_rel
% 3.88/1.01  --clausifier_options                    ""
% 3.88/1.01  --stdin                                 false
% 3.88/1.01  --stats_out                             all
% 3.88/1.01  
% 3.88/1.01  ------ General Options
% 3.88/1.01  
% 3.88/1.01  --fof                                   false
% 3.88/1.01  --time_out_real                         305.
% 3.88/1.01  --time_out_virtual                      -1.
% 3.88/1.01  --symbol_type_check                     false
% 3.88/1.01  --clausify_out                          false
% 3.88/1.01  --sig_cnt_out                           false
% 3.88/1.01  --trig_cnt_out                          false
% 3.88/1.01  --trig_cnt_out_tolerance                1.
% 3.88/1.01  --trig_cnt_out_sk_spl                   false
% 3.88/1.01  --abstr_cl_out                          false
% 3.88/1.01  
% 3.88/1.01  ------ Global Options
% 3.88/1.01  
% 3.88/1.01  --schedule                              default
% 3.88/1.01  --add_important_lit                     false
% 3.88/1.01  --prop_solver_per_cl                    1000
% 3.88/1.01  --min_unsat_core                        false
% 3.88/1.01  --soft_assumptions                      false
% 3.88/1.01  --soft_lemma_size                       3
% 3.88/1.01  --prop_impl_unit_size                   0
% 3.88/1.01  --prop_impl_unit                        []
% 3.88/1.01  --share_sel_clauses                     true
% 3.88/1.01  --reset_solvers                         false
% 3.88/1.01  --bc_imp_inh                            [conj_cone]
% 3.88/1.01  --conj_cone_tolerance                   3.
% 3.88/1.01  --extra_neg_conj                        none
% 3.88/1.01  --large_theory_mode                     true
% 3.88/1.01  --prolific_symb_bound                   200
% 3.88/1.01  --lt_threshold                          2000
% 3.88/1.01  --clause_weak_htbl                      true
% 3.88/1.01  --gc_record_bc_elim                     false
% 3.88/1.01  
% 3.88/1.01  ------ Preprocessing Options
% 3.88/1.01  
% 3.88/1.01  --preprocessing_flag                    true
% 3.88/1.01  --time_out_prep_mult                    0.1
% 3.88/1.01  --splitting_mode                        input
% 3.88/1.01  --splitting_grd                         true
% 3.88/1.01  --splitting_cvd                         false
% 3.88/1.01  --splitting_cvd_svl                     false
% 3.88/1.01  --splitting_nvd                         32
% 3.88/1.01  --sub_typing                            true
% 3.88/1.01  --prep_gs_sim                           true
% 3.88/1.01  --prep_unflatten                        true
% 3.88/1.01  --prep_res_sim                          true
% 3.88/1.01  --prep_upred                            true
% 3.88/1.01  --prep_sem_filter                       exhaustive
% 3.88/1.01  --prep_sem_filter_out                   false
% 3.88/1.01  --pred_elim                             true
% 3.88/1.01  --res_sim_input                         true
% 3.88/1.01  --eq_ax_congr_red                       true
% 3.88/1.01  --pure_diseq_elim                       true
% 3.88/1.01  --brand_transform                       false
% 3.88/1.01  --non_eq_to_eq                          false
% 3.88/1.01  --prep_def_merge                        true
% 3.88/1.01  --prep_def_merge_prop_impl              false
% 3.88/1.01  --prep_def_merge_mbd                    true
% 3.88/1.01  --prep_def_merge_tr_red                 false
% 3.88/1.01  --prep_def_merge_tr_cl                  false
% 3.88/1.01  --smt_preprocessing                     true
% 3.88/1.01  --smt_ac_axioms                         fast
% 3.88/1.01  --preprocessed_out                      false
% 3.88/1.01  --preprocessed_stats                    false
% 3.88/1.01  
% 3.88/1.01  ------ Abstraction refinement Options
% 3.88/1.01  
% 3.88/1.01  --abstr_ref                             []
% 3.88/1.01  --abstr_ref_prep                        false
% 3.88/1.01  --abstr_ref_until_sat                   false
% 3.88/1.01  --abstr_ref_sig_restrict                funpre
% 3.88/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.88/1.01  --abstr_ref_under                       []
% 3.88/1.01  
% 3.88/1.01  ------ SAT Options
% 3.88/1.01  
% 3.88/1.01  --sat_mode                              false
% 3.88/1.01  --sat_fm_restart_options                ""
% 3.88/1.01  --sat_gr_def                            false
% 3.88/1.01  --sat_epr_types                         true
% 3.88/1.01  --sat_non_cyclic_types                  false
% 3.88/1.01  --sat_finite_models                     false
% 3.88/1.01  --sat_fm_lemmas                         false
% 3.88/1.01  --sat_fm_prep                           false
% 3.88/1.01  --sat_fm_uc_incr                        true
% 3.88/1.01  --sat_out_model                         small
% 3.88/1.01  --sat_out_clauses                       false
% 3.88/1.01  
% 3.88/1.01  ------ QBF Options
% 3.88/1.01  
% 3.88/1.01  --qbf_mode                              false
% 3.88/1.01  --qbf_elim_univ                         false
% 3.88/1.01  --qbf_dom_inst                          none
% 3.88/1.01  --qbf_dom_pre_inst                      false
% 3.88/1.01  --qbf_sk_in                             false
% 3.88/1.01  --qbf_pred_elim                         true
% 3.88/1.01  --qbf_split                             512
% 3.88/1.01  
% 3.88/1.01  ------ BMC1 Options
% 3.88/1.01  
% 3.88/1.01  --bmc1_incremental                      false
% 3.88/1.01  --bmc1_axioms                           reachable_all
% 3.88/1.01  --bmc1_min_bound                        0
% 3.88/1.01  --bmc1_max_bound                        -1
% 3.88/1.01  --bmc1_max_bound_default                -1
% 3.88/1.01  --bmc1_symbol_reachability              true
% 3.88/1.01  --bmc1_property_lemmas                  false
% 3.88/1.01  --bmc1_k_induction                      false
% 3.88/1.01  --bmc1_non_equiv_states                 false
% 3.88/1.01  --bmc1_deadlock                         false
% 3.88/1.01  --bmc1_ucm                              false
% 3.88/1.01  --bmc1_add_unsat_core                   none
% 3.88/1.01  --bmc1_unsat_core_children              false
% 3.88/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.88/1.01  --bmc1_out_stat                         full
% 3.88/1.01  --bmc1_ground_init                      false
% 3.88/1.01  --bmc1_pre_inst_next_state              false
% 3.88/1.01  --bmc1_pre_inst_state                   false
% 3.88/1.01  --bmc1_pre_inst_reach_state             false
% 3.88/1.01  --bmc1_out_unsat_core                   false
% 3.88/1.01  --bmc1_aig_witness_out                  false
% 3.88/1.01  --bmc1_verbose                          false
% 3.88/1.01  --bmc1_dump_clauses_tptp                false
% 3.88/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.88/1.01  --bmc1_dump_file                        -
% 3.88/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.88/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.88/1.01  --bmc1_ucm_extend_mode                  1
% 3.88/1.01  --bmc1_ucm_init_mode                    2
% 3.88/1.01  --bmc1_ucm_cone_mode                    none
% 3.88/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.88/1.01  --bmc1_ucm_relax_model                  4
% 3.88/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.88/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.88/1.01  --bmc1_ucm_layered_model                none
% 3.88/1.01  --bmc1_ucm_max_lemma_size               10
% 3.88/1.01  
% 3.88/1.01  ------ AIG Options
% 3.88/1.01  
% 3.88/1.01  --aig_mode                              false
% 3.88/1.01  
% 3.88/1.01  ------ Instantiation Options
% 3.88/1.01  
% 3.88/1.01  --instantiation_flag                    true
% 3.88/1.01  --inst_sos_flag                         true
% 3.88/1.01  --inst_sos_phase                        true
% 3.88/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.88/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.88/1.01  --inst_lit_sel_side                     num_symb
% 3.88/1.01  --inst_solver_per_active                1400
% 3.88/1.01  --inst_solver_calls_frac                1.
% 3.88/1.01  --inst_passive_queue_type               priority_queues
% 3.88/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.88/1.01  --inst_passive_queues_freq              [25;2]
% 3.88/1.01  --inst_dismatching                      true
% 3.88/1.01  --inst_eager_unprocessed_to_passive     true
% 3.88/1.01  --inst_prop_sim_given                   true
% 3.88/1.01  --inst_prop_sim_new                     false
% 3.88/1.01  --inst_subs_new                         false
% 3.88/1.01  --inst_eq_res_simp                      false
% 3.88/1.01  --inst_subs_given                       false
% 3.88/1.01  --inst_orphan_elimination               true
% 3.88/1.01  --inst_learning_loop_flag               true
% 3.88/1.01  --inst_learning_start                   3000
% 3.88/1.01  --inst_learning_factor                  2
% 3.88/1.01  --inst_start_prop_sim_after_learn       3
% 3.88/1.01  --inst_sel_renew                        solver
% 3.88/1.01  --inst_lit_activity_flag                true
% 3.88/1.01  --inst_restr_to_given                   false
% 3.88/1.01  --inst_activity_threshold               500
% 3.88/1.01  --inst_out_proof                        true
% 3.88/1.01  
% 3.88/1.01  ------ Resolution Options
% 3.88/1.01  
% 3.88/1.01  --resolution_flag                       true
% 3.88/1.01  --res_lit_sel                           adaptive
% 3.88/1.01  --res_lit_sel_side                      none
% 3.88/1.01  --res_ordering                          kbo
% 3.88/1.01  --res_to_prop_solver                    active
% 3.88/1.01  --res_prop_simpl_new                    false
% 3.88/1.01  --res_prop_simpl_given                  true
% 3.88/1.01  --res_passive_queue_type                priority_queues
% 3.88/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.88/1.01  --res_passive_queues_freq               [15;5]
% 3.88/1.01  --res_forward_subs                      full
% 3.88/1.01  --res_backward_subs                     full
% 3.88/1.01  --res_forward_subs_resolution           true
% 3.88/1.01  --res_backward_subs_resolution          true
% 3.88/1.01  --res_orphan_elimination                true
% 3.88/1.01  --res_time_limit                        2.
% 3.88/1.01  --res_out_proof                         true
% 3.88/1.01  
% 3.88/1.01  ------ Superposition Options
% 3.88/1.01  
% 3.88/1.01  --superposition_flag                    true
% 3.88/1.01  --sup_passive_queue_type                priority_queues
% 3.88/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.88/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.88/1.01  --demod_completeness_check              fast
% 3.88/1.01  --demod_use_ground                      true
% 3.88/1.01  --sup_to_prop_solver                    passive
% 3.88/1.01  --sup_prop_simpl_new                    true
% 3.88/1.01  --sup_prop_simpl_given                  true
% 3.88/1.01  --sup_fun_splitting                     true
% 3.88/1.01  --sup_smt_interval                      50000
% 3.88/1.01  
% 3.88/1.01  ------ Superposition Simplification Setup
% 3.88/1.01  
% 3.88/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.88/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.88/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.88/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.88/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.88/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.88/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.88/1.01  --sup_immed_triv                        [TrivRules]
% 3.88/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.88/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.88/1.01  --sup_immed_bw_main                     []
% 3.88/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.88/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.88/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.88/1.01  --sup_input_bw                          []
% 3.88/1.01  
% 3.88/1.01  ------ Combination Options
% 3.88/1.01  
% 3.88/1.01  --comb_res_mult                         3
% 3.88/1.01  --comb_sup_mult                         2
% 3.88/1.01  --comb_inst_mult                        10
% 3.88/1.01  
% 3.88/1.01  ------ Debug Options
% 3.88/1.01  
% 3.88/1.01  --dbg_backtrace                         false
% 3.88/1.01  --dbg_dump_prop_clauses                 false
% 3.88/1.01  --dbg_dump_prop_clauses_file            -
% 3.88/1.01  --dbg_out_stat                          false
% 3.88/1.01  ------ Parsing...
% 3.88/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.88/1.01  
% 3.88/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.88/1.01  
% 3.88/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.88/1.01  
% 3.88/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/1.01  ------ Proving...
% 3.88/1.01  ------ Problem Properties 
% 3.88/1.01  
% 3.88/1.01  
% 3.88/1.01  clauses                                 47
% 3.88/1.01  conjectures                             23
% 3.88/1.01  EPR                                     13
% 3.88/1.01  Horn                                    31
% 3.88/1.01  unary                                   14
% 3.88/1.01  binary                                  18
% 3.88/1.01  lits                                    163
% 3.88/1.01  lits eq                                 4
% 3.88/1.01  fd_pure                                 0
% 3.88/1.01  fd_pseudo                               0
% 3.88/1.01  fd_cond                                 0
% 3.88/1.01  fd_pseudo_cond                          0
% 3.88/1.01  AC symbols                              0
% 3.88/1.01  
% 3.88/1.01  ------ Schedule dynamic 5 is on 
% 3.88/1.01  
% 3.88/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.88/1.01  
% 3.88/1.01  
% 3.88/1.01  ------ 
% 3.88/1.01  Current options:
% 3.88/1.01  ------ 
% 3.88/1.01  
% 3.88/1.01  ------ Input Options
% 3.88/1.01  
% 3.88/1.01  --out_options                           all
% 3.88/1.01  --tptp_safe_out                         true
% 3.88/1.01  --problem_path                          ""
% 3.88/1.01  --include_path                          ""
% 3.88/1.01  --clausifier                            res/vclausify_rel
% 3.88/1.01  --clausifier_options                    ""
% 3.88/1.01  --stdin                                 false
% 3.88/1.01  --stats_out                             all
% 3.88/1.01  
% 3.88/1.01  ------ General Options
% 3.88/1.01  
% 3.88/1.01  --fof                                   false
% 3.88/1.01  --time_out_real                         305.
% 3.88/1.01  --time_out_virtual                      -1.
% 3.88/1.01  --symbol_type_check                     false
% 3.88/1.01  --clausify_out                          false
% 3.88/1.01  --sig_cnt_out                           false
% 3.88/1.01  --trig_cnt_out                          false
% 3.88/1.01  --trig_cnt_out_tolerance                1.
% 3.88/1.01  --trig_cnt_out_sk_spl                   false
% 3.88/1.01  --abstr_cl_out                          false
% 3.88/1.01  
% 3.88/1.01  ------ Global Options
% 3.88/1.01  
% 3.88/1.01  --schedule                              default
% 3.88/1.01  --add_important_lit                     false
% 3.88/1.01  --prop_solver_per_cl                    1000
% 3.88/1.01  --min_unsat_core                        false
% 3.88/1.01  --soft_assumptions                      false
% 3.88/1.01  --soft_lemma_size                       3
% 3.88/1.01  --prop_impl_unit_size                   0
% 3.88/1.01  --prop_impl_unit                        []
% 3.88/1.01  --share_sel_clauses                     true
% 3.88/1.01  --reset_solvers                         false
% 3.88/1.01  --bc_imp_inh                            [conj_cone]
% 3.88/1.01  --conj_cone_tolerance                   3.
% 3.88/1.01  --extra_neg_conj                        none
% 3.88/1.01  --large_theory_mode                     true
% 3.88/1.01  --prolific_symb_bound                   200
% 3.88/1.01  --lt_threshold                          2000
% 3.88/1.01  --clause_weak_htbl                      true
% 3.88/1.01  --gc_record_bc_elim                     false
% 3.88/1.01  
% 3.88/1.01  ------ Preprocessing Options
% 3.88/1.01  
% 3.88/1.01  --preprocessing_flag                    true
% 3.88/1.01  --time_out_prep_mult                    0.1
% 3.88/1.01  --splitting_mode                        input
% 3.88/1.01  --splitting_grd                         true
% 3.88/1.01  --splitting_cvd                         false
% 3.88/1.01  --splitting_cvd_svl                     false
% 3.88/1.01  --splitting_nvd                         32
% 3.88/1.01  --sub_typing                            true
% 3.88/1.01  --prep_gs_sim                           true
% 3.88/1.01  --prep_unflatten                        true
% 3.88/1.01  --prep_res_sim                          true
% 3.88/1.01  --prep_upred                            true
% 3.88/1.01  --prep_sem_filter                       exhaustive
% 3.88/1.01  --prep_sem_filter_out                   false
% 3.88/1.01  --pred_elim                             true
% 3.88/1.01  --res_sim_input                         true
% 3.88/1.01  --eq_ax_congr_red                       true
% 3.88/1.01  --pure_diseq_elim                       true
% 3.88/1.01  --brand_transform                       false
% 3.88/1.01  --non_eq_to_eq                          false
% 3.88/1.01  --prep_def_merge                        true
% 3.88/1.01  --prep_def_merge_prop_impl              false
% 3.88/1.01  --prep_def_merge_mbd                    true
% 3.88/1.01  --prep_def_merge_tr_red                 false
% 3.88/1.01  --prep_def_merge_tr_cl                  false
% 3.88/1.01  --smt_preprocessing                     true
% 3.88/1.01  --smt_ac_axioms                         fast
% 3.88/1.01  --preprocessed_out                      false
% 3.88/1.01  --preprocessed_stats                    false
% 3.88/1.01  
% 3.88/1.01  ------ Abstraction refinement Options
% 3.88/1.01  
% 3.88/1.01  --abstr_ref                             []
% 3.88/1.01  --abstr_ref_prep                        false
% 3.88/1.01  --abstr_ref_until_sat                   false
% 3.88/1.01  --abstr_ref_sig_restrict                funpre
% 3.88/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.88/1.01  --abstr_ref_under                       []
% 3.88/1.01  
% 3.88/1.01  ------ SAT Options
% 3.88/1.01  
% 3.88/1.01  --sat_mode                              false
% 3.88/1.01  --sat_fm_restart_options                ""
% 3.88/1.01  --sat_gr_def                            false
% 3.88/1.01  --sat_epr_types                         true
% 3.88/1.01  --sat_non_cyclic_types                  false
% 3.88/1.01  --sat_finite_models                     false
% 3.88/1.01  --sat_fm_lemmas                         false
% 3.88/1.01  --sat_fm_prep                           false
% 3.88/1.01  --sat_fm_uc_incr                        true
% 3.88/1.01  --sat_out_model                         small
% 3.88/1.01  --sat_out_clauses                       false
% 3.88/1.01  
% 3.88/1.01  ------ QBF Options
% 3.88/1.01  
% 3.88/1.01  --qbf_mode                              false
% 3.88/1.01  --qbf_elim_univ                         false
% 3.88/1.01  --qbf_dom_inst                          none
% 3.88/1.01  --qbf_dom_pre_inst                      false
% 3.88/1.01  --qbf_sk_in                             false
% 3.88/1.01  --qbf_pred_elim                         true
% 3.88/1.01  --qbf_split                             512
% 3.88/1.01  
% 3.88/1.01  ------ BMC1 Options
% 3.88/1.01  
% 3.88/1.01  --bmc1_incremental                      false
% 3.88/1.01  --bmc1_axioms                           reachable_all
% 3.88/1.01  --bmc1_min_bound                        0
% 3.88/1.01  --bmc1_max_bound                        -1
% 3.88/1.01  --bmc1_max_bound_default                -1
% 3.88/1.01  --bmc1_symbol_reachability              true
% 3.88/1.01  --bmc1_property_lemmas                  false
% 3.88/1.01  --bmc1_k_induction                      false
% 3.88/1.01  --bmc1_non_equiv_states                 false
% 3.88/1.01  --bmc1_deadlock                         false
% 3.88/1.01  --bmc1_ucm                              false
% 3.88/1.01  --bmc1_add_unsat_core                   none
% 3.88/1.01  --bmc1_unsat_core_children              false
% 3.88/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.88/1.01  --bmc1_out_stat                         full
% 3.88/1.01  --bmc1_ground_init                      false
% 3.88/1.01  --bmc1_pre_inst_next_state              false
% 3.88/1.01  --bmc1_pre_inst_state                   false
% 3.88/1.01  --bmc1_pre_inst_reach_state             false
% 3.88/1.01  --bmc1_out_unsat_core                   false
% 3.88/1.01  --bmc1_aig_witness_out                  false
% 3.88/1.01  --bmc1_verbose                          false
% 3.88/1.01  --bmc1_dump_clauses_tptp                false
% 3.88/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.88/1.01  --bmc1_dump_file                        -
% 3.88/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.88/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.88/1.01  --bmc1_ucm_extend_mode                  1
% 3.88/1.01  --bmc1_ucm_init_mode                    2
% 3.88/1.01  --bmc1_ucm_cone_mode                    none
% 3.88/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.88/1.01  --bmc1_ucm_relax_model                  4
% 3.88/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.88/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.88/1.01  --bmc1_ucm_layered_model                none
% 3.88/1.01  --bmc1_ucm_max_lemma_size               10
% 3.88/1.01  
% 3.88/1.01  ------ AIG Options
% 3.88/1.01  
% 3.88/1.01  --aig_mode                              false
% 3.88/1.01  
% 3.88/1.01  ------ Instantiation Options
% 3.88/1.01  
% 3.88/1.01  --instantiation_flag                    true
% 3.88/1.01  --inst_sos_flag                         true
% 3.88/1.01  --inst_sos_phase                        true
% 3.88/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.88/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.88/1.01  --inst_lit_sel_side                     none
% 3.88/1.01  --inst_solver_per_active                1400
% 3.88/1.01  --inst_solver_calls_frac                1.
% 3.88/1.01  --inst_passive_queue_type               priority_queues
% 3.88/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.88/1.01  --inst_passive_queues_freq              [25;2]
% 3.88/1.01  --inst_dismatching                      true
% 3.88/1.01  --inst_eager_unprocessed_to_passive     true
% 3.88/1.01  --inst_prop_sim_given                   true
% 3.88/1.01  --inst_prop_sim_new                     false
% 3.88/1.01  --inst_subs_new                         false
% 3.88/1.01  --inst_eq_res_simp                      false
% 3.88/1.01  --inst_subs_given                       false
% 3.88/1.01  --inst_orphan_elimination               true
% 3.88/1.01  --inst_learning_loop_flag               true
% 3.88/1.01  --inst_learning_start                   3000
% 3.88/1.01  --inst_learning_factor                  2
% 3.88/1.01  --inst_start_prop_sim_after_learn       3
% 3.88/1.01  --inst_sel_renew                        solver
% 3.88/1.01  --inst_lit_activity_flag                true
% 3.88/1.01  --inst_restr_to_given                   false
% 3.88/1.01  --inst_activity_threshold               500
% 3.88/1.01  --inst_out_proof                        true
% 3.88/1.01  
% 3.88/1.01  ------ Resolution Options
% 3.88/1.01  
% 3.88/1.01  --resolution_flag                       false
% 3.88/1.01  --res_lit_sel                           adaptive
% 3.88/1.01  --res_lit_sel_side                      none
% 3.88/1.01  --res_ordering                          kbo
% 3.88/1.01  --res_to_prop_solver                    active
% 3.88/1.01  --res_prop_simpl_new                    false
% 3.88/1.01  --res_prop_simpl_given                  true
% 3.88/1.01  --res_passive_queue_type                priority_queues
% 3.88/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.88/1.01  --res_passive_queues_freq               [15;5]
% 3.88/1.01  --res_forward_subs                      full
% 3.88/1.01  --res_backward_subs                     full
% 3.88/1.01  --res_forward_subs_resolution           true
% 3.88/1.01  --res_backward_subs_resolution          true
% 3.88/1.01  --res_orphan_elimination                true
% 3.88/1.01  --res_time_limit                        2.
% 3.88/1.01  --res_out_proof                         true
% 3.88/1.01  
% 3.88/1.01  ------ Superposition Options
% 3.88/1.01  
% 3.88/1.01  --superposition_flag                    true
% 3.88/1.01  --sup_passive_queue_type                priority_queues
% 3.88/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.88/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.88/1.01  --demod_completeness_check              fast
% 3.88/1.01  --demod_use_ground                      true
% 3.88/1.01  --sup_to_prop_solver                    passive
% 3.88/1.01  --sup_prop_simpl_new                    true
% 3.88/1.01  --sup_prop_simpl_given                  true
% 3.88/1.01  --sup_fun_splitting                     true
% 3.88/1.01  --sup_smt_interval                      50000
% 3.88/1.01  
% 3.88/1.01  ------ Superposition Simplification Setup
% 3.88/1.01  
% 3.88/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.88/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.88/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.88/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.88/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.88/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.88/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.88/1.01  --sup_immed_triv                        [TrivRules]
% 3.88/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.88/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.88/1.01  --sup_immed_bw_main                     []
% 3.88/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.88/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.88/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.88/1.01  --sup_input_bw                          []
% 3.88/1.01  
% 3.88/1.01  ------ Combination Options
% 3.88/1.01  
% 3.88/1.01  --comb_res_mult                         3
% 3.88/1.01  --comb_sup_mult                         2
% 3.88/1.01  --comb_inst_mult                        10
% 3.88/1.01  
% 3.88/1.01  ------ Debug Options
% 3.88/1.01  
% 3.88/1.01  --dbg_backtrace                         false
% 3.88/1.01  --dbg_dump_prop_clauses                 false
% 3.88/1.01  --dbg_dump_prop_clauses_file            -
% 3.88/1.01  --dbg_out_stat                          false
% 3.88/1.01  
% 3.88/1.01  
% 3.88/1.01  
% 3.88/1.01  
% 3.88/1.01  ------ Proving...
% 3.88/1.01  
% 3.88/1.01  
% 3.88/1.01  % SZS status Theorem for theBenchmark.p
% 3.88/1.01  
% 3.88/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.88/1.01  
% 3.88/1.01  fof(f12,conjecture,(
% 3.88/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 3.88/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.01  
% 3.88/1.01  fof(f13,negated_conjecture,(
% 3.88/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 3.88/1.01    inference(negated_conjecture,[],[f12])).
% 3.88/1.01  
% 3.88/1.01  fof(f33,plain,(
% 3.88/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & (r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0)) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.88/1.01    inference(ennf_transformation,[],[f13])).
% 3.88/1.01  
% 3.88/1.01  fof(f34,plain,(
% 3.88/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.88/1.01    inference(flattening,[],[f33])).
% 3.88/1.01  
% 3.88/1.01  fof(f45,plain,(
% 3.88/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.88/1.01    inference(nnf_transformation,[],[f34])).
% 3.88/1.01  
% 3.88/1.01  fof(f46,plain,(
% 3.88/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.88/1.01    inference(flattening,[],[f45])).
% 3.88/1.01  
% 3.88/1.01  fof(f51,plain,(
% 3.88/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((~m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,sK6) & k1_tsep_1(X0,X3,sK6) = X0 & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 3.88/1.01    introduced(choice_axiom,[])).
% 3.88/1.01  
% 3.88/1.01  fof(f50,plain,(
% 3.88/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK5)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK5))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,sK5,X4) & k1_tsep_1(X0,sK5,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 3.88/1.01    introduced(choice_axiom,[])).
% 3.88/1.01  
% 3.88/1.01  fof(f49,plain,(
% 3.88/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(sK4,X0,X1) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) & m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X3))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK4,X0,X1) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.88/1.01    introduced(choice_axiom,[])).
% 3.88/1.01  
% 3.88/1.01  fof(f48,plain,(
% 3.88/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(X2,X0,sK3) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) & m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v5_pre_topc(X2,X0,sK3) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 3.88/1.01    introduced(choice_axiom,[])).
% 3.88/1.01  
% 3.88/1.01  fof(f47,plain,(
% 3.88/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(sK2,X3,X4) & k1_tsep_1(sK2,X3,X4) = sK2 & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.88/1.01    introduced(choice_axiom,[])).
% 3.88/1.01  
% 3.88/1.01  fof(f52,plain,(
% 3.88/1.01    (((((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,sK5,sK6) & k1_tsep_1(sK2,sK5,sK6) = sK2 & m1_pre_topc(sK6,sK2) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.88/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f46,f51,f50,f49,f48,f47])).
% 3.88/1.01  
% 3.88/1.01  fof(f95,plain,(
% 3.88/1.01    k1_tsep_1(sK2,sK5,sK6) = sK2),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  fof(f9,axiom,(
% 3.88/1.01    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.88/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.01  
% 3.88/1.01  fof(f14,plain,(
% 3.88/1.01    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.88/1.01    inference(pure_predicate_removal,[],[f9])).
% 3.88/1.01  
% 3.88/1.01  fof(f27,plain,(
% 3.88/1.01    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.88/1.01    inference(ennf_transformation,[],[f14])).
% 3.88/1.01  
% 3.88/1.01  fof(f28,plain,(
% 3.88/1.01    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.88/1.01    inference(flattening,[],[f27])).
% 3.88/1.01  
% 3.88/1.01  fof(f63,plain,(
% 3.88/1.01    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.88/1.01    inference(cnf_transformation,[],[f28])).
% 3.88/1.01  
% 3.88/1.01  fof(f82,plain,(
% 3.88/1.01    ~v2_struct_0(sK2)),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  fof(f84,plain,(
% 3.88/1.01    l1_pre_topc(sK2)),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  fof(f91,plain,(
% 3.88/1.01    ~v2_struct_0(sK5)),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  fof(f92,plain,(
% 3.88/1.01    m1_pre_topc(sK5,sK2)),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  fof(f93,plain,(
% 3.88/1.01    ~v2_struct_0(sK6)),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  fof(f94,plain,(
% 3.88/1.01    m1_pre_topc(sK6,sK2)),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  fof(f90,plain,(
% 3.88/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  fof(f8,axiom,(
% 3.88/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 3.88/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.01  
% 3.88/1.01  fof(f25,plain,(
% 3.88/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.88/1.01    inference(ennf_transformation,[],[f8])).
% 3.88/1.01  
% 3.88/1.01  fof(f26,plain,(
% 3.88/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.88/1.01    inference(flattening,[],[f25])).
% 3.88/1.01  
% 3.88/1.01  fof(f61,plain,(
% 3.88/1.01    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.88/1.01    inference(cnf_transformation,[],[f26])).
% 3.88/1.01  
% 3.88/1.01  fof(f83,plain,(
% 3.88/1.01    v2_pre_topc(sK2)),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  fof(f85,plain,(
% 3.88/1.01    ~v2_struct_0(sK3)),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  fof(f86,plain,(
% 3.88/1.01    v2_pre_topc(sK3)),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  fof(f87,plain,(
% 3.88/1.01    l1_pre_topc(sK3)),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  fof(f88,plain,(
% 3.88/1.01    v1_funct_1(sK4)),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  fof(f89,plain,(
% 3.88/1.01    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  fof(f5,axiom,(
% 3.88/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.88/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.01  
% 3.88/1.01  fof(f21,plain,(
% 3.88/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.88/1.01    inference(ennf_transformation,[],[f5])).
% 3.88/1.01  
% 3.88/1.01  fof(f22,plain,(
% 3.88/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.88/1.01    inference(flattening,[],[f21])).
% 3.88/1.01  
% 3.88/1.01  fof(f58,plain,(
% 3.88/1.01    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.88/1.01    inference(cnf_transformation,[],[f22])).
% 3.88/1.01  
% 3.88/1.01  fof(f36,plain,(
% 3.88/1.01    ! [X2,X0,X4,X3,X1] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> sP0(X1,X3,X4,X0,X2)) | ~sP1(X2,X0,X4,X3,X1))),
% 3.88/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.88/1.01  
% 3.88/1.01  fof(f39,plain,(
% 3.88/1.01    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))))) | ~sP1(X2,X0,X4,X3,X1))),
% 3.88/1.01    inference(nnf_transformation,[],[f36])).
% 3.88/1.01  
% 3.88/1.01  fof(f40,plain,(
% 3.88/1.01    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))))) | ~sP1(X2,X0,X4,X3,X1))),
% 3.88/1.01    inference(flattening,[],[f39])).
% 3.88/1.01  
% 3.88/1.01  fof(f41,plain,(
% 3.88/1.01    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) & v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) & v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) & v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))))) | ~sP1(X0,X1,X2,X3,X4))),
% 3.88/1.01    inference(rectify,[],[f40])).
% 3.88/1.01  
% 3.88/1.01  fof(f67,plain,(
% 3.88/1.01    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) | ~sP1(X0,X1,X2,X3,X4)) )),
% 3.88/1.01    inference(cnf_transformation,[],[f41])).
% 3.88/1.01  
% 3.88/1.01  fof(f11,axiom,(
% 3.88/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))))))))),
% 3.88/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.01  
% 3.88/1.01  fof(f31,plain,(
% 3.88/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.88/1.01    inference(ennf_transformation,[],[f11])).
% 3.88/1.01  
% 3.88/1.01  fof(f32,plain,(
% 3.88/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.88/1.01    inference(flattening,[],[f31])).
% 3.88/1.01  
% 3.88/1.01  fof(f35,plain,(
% 3.88/1.01    ! [X1,X3,X4,X0,X2] : (sP0(X1,X3,X4,X0,X2) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))),
% 3.88/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.88/1.01  
% 3.88/1.01  fof(f37,plain,(
% 3.88/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X2,X0,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.88/1.01    inference(definition_folding,[],[f32,f36,f35])).
% 3.88/1.01  
% 3.88/1.01  fof(f81,plain,(
% 3.88/1.01    ( ! [X4,X2,X0,X3,X1] : (sP1(X2,X0,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.88/1.01    inference(cnf_transformation,[],[f37])).
% 3.88/1.01  
% 3.88/1.01  fof(f96,plain,(
% 3.88/1.01    r4_tsep_1(sK2,sK5,sK6)),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  fof(f71,plain,(
% 3.88/1.01    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 3.88/1.01    inference(cnf_transformation,[],[f41])).
% 3.88/1.01  
% 3.88/1.01  fof(f6,axiom,(
% 3.88/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.88/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.01  
% 3.88/1.01  fof(f23,plain,(
% 3.88/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.88/1.01    inference(ennf_transformation,[],[f6])).
% 3.88/1.01  
% 3.88/1.01  fof(f59,plain,(
% 3.88/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.88/1.01    inference(cnf_transformation,[],[f23])).
% 3.88/1.01  
% 3.88/1.01  fof(f10,axiom,(
% 3.88/1.01    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 3.88/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.01  
% 3.88/1.01  fof(f29,plain,(
% 3.88/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 3.88/1.01    inference(ennf_transformation,[],[f10])).
% 3.88/1.01  
% 3.88/1.01  fof(f30,plain,(
% 3.88/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 3.88/1.01    inference(flattening,[],[f29])).
% 3.88/1.01  
% 3.88/1.01  fof(f66,plain,(
% 3.88/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.88/1.01    inference(cnf_transformation,[],[f30])).
% 3.88/1.01  
% 3.88/1.01  fof(f70,plain,(
% 3.88/1.01    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 3.88/1.01    inference(cnf_transformation,[],[f41])).
% 3.88/1.01  
% 3.88/1.01  fof(f65,plain,(
% 3.88/1.01    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.88/1.01    inference(cnf_transformation,[],[f30])).
% 3.88/1.01  
% 3.88/1.01  fof(f64,plain,(
% 3.88/1.01    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.88/1.01    inference(cnf_transformation,[],[f30])).
% 3.88/1.01  
% 3.88/1.01  fof(f4,axiom,(
% 3.88/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.88/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.01  
% 3.88/1.01  fof(f15,plain,(
% 3.88/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.88/1.01    inference(pure_predicate_removal,[],[f4])).
% 3.88/1.01  
% 3.88/1.01  fof(f20,plain,(
% 3.88/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/1.01    inference(ennf_transformation,[],[f15])).
% 3.88/1.01  
% 3.88/1.01  fof(f57,plain,(
% 3.88/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.88/1.01    inference(cnf_transformation,[],[f20])).
% 3.88/1.01  
% 3.88/1.01  fof(f1,axiom,(
% 3.88/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.88/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.01  
% 3.88/1.01  fof(f16,plain,(
% 3.88/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.88/1.01    inference(ennf_transformation,[],[f1])).
% 3.88/1.01  
% 3.88/1.01  fof(f38,plain,(
% 3.88/1.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.88/1.01    inference(nnf_transformation,[],[f16])).
% 3.88/1.01  
% 3.88/1.01  fof(f53,plain,(
% 3.88/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.88/1.01    inference(cnf_transformation,[],[f38])).
% 3.88/1.01  
% 3.88/1.01  fof(f3,axiom,(
% 3.88/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.88/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.01  
% 3.88/1.01  fof(f19,plain,(
% 3.88/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/1.01    inference(ennf_transformation,[],[f3])).
% 3.88/1.01  
% 3.88/1.01  fof(f56,plain,(
% 3.88/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.88/1.01    inference(cnf_transformation,[],[f19])).
% 3.88/1.01  
% 3.88/1.01  fof(f2,axiom,(
% 3.88/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.88/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.01  
% 3.88/1.01  fof(f17,plain,(
% 3.88/1.01    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.88/1.01    inference(ennf_transformation,[],[f2])).
% 3.88/1.01  
% 3.88/1.01  fof(f18,plain,(
% 3.88/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.88/1.01    inference(flattening,[],[f17])).
% 3.88/1.01  
% 3.88/1.01  fof(f55,plain,(
% 3.88/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.88/1.01    inference(cnf_transformation,[],[f18])).
% 3.88/1.01  
% 3.88/1.01  fof(f103,plain,(
% 3.88/1.01    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  fof(f107,plain,(
% 3.88/1.01    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  fof(f111,plain,(
% 3.88/1.01    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  fof(f119,plain,(
% 3.88/1.01    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  fof(f123,plain,(
% 3.88/1.01    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  fof(f127,plain,(
% 3.88/1.01    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  fof(f42,plain,(
% 3.88/1.01    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 3.88/1.01    inference(nnf_transformation,[],[f35])).
% 3.88/1.01  
% 3.88/1.01  fof(f43,plain,(
% 3.88/1.01    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 3.88/1.01    inference(flattening,[],[f42])).
% 3.88/1.01  
% 3.88/1.01  fof(f44,plain,(
% 3.88/1.01    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) & ((m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 3.88/1.01    inference(rectify,[],[f43])).
% 3.88/1.01  
% 3.88/1.01  fof(f80,plain,(
% 3.88/1.01    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) )),
% 3.88/1.01    inference(cnf_transformation,[],[f44])).
% 3.88/1.01  
% 3.88/1.01  fof(f7,axiom,(
% 3.88/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.88/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.01  
% 3.88/1.01  fof(f24,plain,(
% 3.88/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.88/1.01    inference(ennf_transformation,[],[f7])).
% 3.88/1.01  
% 3.88/1.01  fof(f60,plain,(
% 3.88/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.88/1.01    inference(cnf_transformation,[],[f24])).
% 3.88/1.01  
% 3.88/1.01  fof(f74,plain,(
% 3.88/1.01    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.88/1.01    inference(cnf_transformation,[],[f44])).
% 3.88/1.01  
% 3.88/1.01  fof(f78,plain,(
% 3.88/1.01    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.88/1.01    inference(cnf_transformation,[],[f44])).
% 3.88/1.01  
% 3.88/1.01  fof(f129,plain,(
% 3.88/1.01    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 3.88/1.01    inference(cnf_transformation,[],[f52])).
% 3.88/1.01  
% 3.88/1.01  cnf(c_63,negated_conjecture,
% 3.88/1.01      ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
% 3.88/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2417,negated_conjecture,
% 3.88/1.01      ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
% 3.88/1.01      inference(subtyping,[status(esa)],[c_63]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_9,plain,
% 3.88/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.88/1.01      | ~ m1_pre_topc(X2,X1)
% 3.88/1.01      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 3.88/1.01      | v2_struct_0(X1)
% 3.88/1.01      | v2_struct_0(X0)
% 3.88/1.01      | v2_struct_0(X2)
% 3.88/1.01      | ~ l1_pre_topc(X1) ),
% 3.88/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2439,plain,
% 3.88/1.01      ( ~ m1_pre_topc(X0_56,X1_56)
% 3.88/1.01      | ~ m1_pre_topc(X2_56,X1_56)
% 3.88/1.01      | m1_pre_topc(k1_tsep_1(X1_56,X0_56,X2_56),X1_56)
% 3.88/1.01      | v2_struct_0(X0_56)
% 3.88/1.01      | v2_struct_0(X1_56)
% 3.88/1.01      | v2_struct_0(X2_56)
% 3.88/1.01      | ~ l1_pre_topc(X1_56) ),
% 3.88/1.01      inference(subtyping,[status(esa)],[c_9]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3293,plain,
% 3.88/1.01      ( m1_pre_topc(X0_56,X1_56) != iProver_top
% 3.88/1.01      | m1_pre_topc(X2_56,X1_56) != iProver_top
% 3.88/1.01      | m1_pre_topc(k1_tsep_1(X1_56,X0_56,X2_56),X1_56) = iProver_top
% 3.88/1.01      | v2_struct_0(X1_56) = iProver_top
% 3.88/1.01      | v2_struct_0(X0_56) = iProver_top
% 3.88/1.01      | v2_struct_0(X2_56) = iProver_top
% 3.88/1.01      | l1_pre_topc(X1_56) != iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_2439]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_5511,plain,
% 3.88/1.01      ( m1_pre_topc(sK5,sK2) != iProver_top
% 3.88/1.01      | m1_pre_topc(sK6,sK2) != iProver_top
% 3.88/1.01      | m1_pre_topc(sK2,sK2) = iProver_top
% 3.88/1.01      | v2_struct_0(sK5) = iProver_top
% 3.88/1.01      | v2_struct_0(sK6) = iProver_top
% 3.88/1.01      | v2_struct_0(sK2) = iProver_top
% 3.88/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_2417,c_3293]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_76,negated_conjecture,
% 3.88/1.01      ( ~ v2_struct_0(sK2) ),
% 3.88/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_77,plain,
% 3.88/1.01      ( v2_struct_0(sK2) != iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_76]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_74,negated_conjecture,
% 3.88/1.01      ( l1_pre_topc(sK2) ),
% 3.88/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_79,plain,
% 3.88/1.01      ( l1_pre_topc(sK2) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_74]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_67,negated_conjecture,
% 3.88/1.01      ( ~ v2_struct_0(sK5) ),
% 3.88/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_86,plain,
% 3.88/1.01      ( v2_struct_0(sK5) != iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_67]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_66,negated_conjecture,
% 3.88/1.01      ( m1_pre_topc(sK5,sK2) ),
% 3.88/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_87,plain,
% 3.88/1.01      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_66]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_65,negated_conjecture,
% 3.88/1.01      ( ~ v2_struct_0(sK6) ),
% 3.88/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_88,plain,
% 3.88/1.01      ( v2_struct_0(sK6) != iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_65]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_64,negated_conjecture,
% 3.88/1.01      ( m1_pre_topc(sK6,sK2) ),
% 3.88/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_89,plain,
% 3.88/1.01      ( m1_pre_topc(sK6,sK2) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_64]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3474,plain,
% 3.88/1.01      ( ~ m1_pre_topc(X0_56,X1_56)
% 3.88/1.01      | m1_pre_topc(k1_tsep_1(X1_56,sK5,X0_56),X1_56)
% 3.88/1.01      | ~ m1_pre_topc(sK5,X1_56)
% 3.88/1.01      | v2_struct_0(X1_56)
% 3.88/1.01      | v2_struct_0(X0_56)
% 3.88/1.01      | v2_struct_0(sK5)
% 3.88/1.01      | ~ l1_pre_topc(X1_56) ),
% 3.88/1.01      inference(instantiation,[status(thm)],[c_2439]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3623,plain,
% 3.88/1.01      ( ~ m1_pre_topc(X0_56,sK2)
% 3.88/1.01      | m1_pre_topc(k1_tsep_1(sK2,sK5,X0_56),sK2)
% 3.88/1.01      | ~ m1_pre_topc(sK5,sK2)
% 3.88/1.01      | v2_struct_0(X0_56)
% 3.88/1.01      | v2_struct_0(sK5)
% 3.88/1.01      | v2_struct_0(sK2)
% 3.88/1.01      | ~ l1_pre_topc(sK2) ),
% 3.88/1.01      inference(instantiation,[status(thm)],[c_3474]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3892,plain,
% 3.88/1.01      ( m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2)
% 3.88/1.01      | ~ m1_pre_topc(sK5,sK2)
% 3.88/1.01      | ~ m1_pre_topc(sK6,sK2)
% 3.88/1.01      | v2_struct_0(sK5)
% 3.88/1.01      | v2_struct_0(sK6)
% 3.88/1.01      | v2_struct_0(sK2)
% 3.88/1.01      | ~ l1_pre_topc(sK2) ),
% 3.88/1.01      inference(instantiation,[status(thm)],[c_3623]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3893,plain,
% 3.88/1.01      ( m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2) = iProver_top
% 3.88/1.01      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.88/1.01      | m1_pre_topc(sK6,sK2) != iProver_top
% 3.88/1.01      | v2_struct_0(sK5) = iProver_top
% 3.88/1.01      | v2_struct_0(sK6) = iProver_top
% 3.88/1.01      | v2_struct_0(sK2) = iProver_top
% 3.88/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_3892]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2445,plain,( X0_56 = X0_56 ),theory(equality) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3957,plain,
% 3.88/1.01      ( sK2 = sK2 ),
% 3.88/1.01      inference(instantiation,[status(thm)],[c_2445]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2450,plain,
% 3.88/1.01      ( X0_56 != X1_56 | X2_56 != X1_56 | X2_56 = X0_56 ),
% 3.88/1.01      theory(equality) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3803,plain,
% 3.88/1.01      ( X0_56 != X1_56 | sK2 != X1_56 | sK2 = X0_56 ),
% 3.88/1.01      inference(instantiation,[status(thm)],[c_2450]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3959,plain,
% 3.88/1.01      ( X0_56 != sK2 | sK2 = X0_56 | sK2 != sK2 ),
% 3.88/1.01      inference(instantiation,[status(thm)],[c_3803]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_4391,plain,
% 3.88/1.01      ( k1_tsep_1(sK2,sK5,sK6) != sK2
% 3.88/1.01      | sK2 = k1_tsep_1(sK2,sK5,sK6)
% 3.88/1.01      | sK2 != sK2 ),
% 3.88/1.01      inference(instantiation,[status(thm)],[c_3959]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2458,plain,
% 3.88/1.01      ( ~ m1_pre_topc(X0_56,X1_56)
% 3.88/1.01      | m1_pre_topc(X2_56,X3_56)
% 3.88/1.01      | X2_56 != X0_56
% 3.88/1.01      | X3_56 != X1_56 ),
% 3.88/1.01      theory(equality) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3645,plain,
% 3.88/1.01      ( ~ m1_pre_topc(X0_56,X1_56)
% 3.88/1.01      | m1_pre_topc(X2_56,sK2)
% 3.88/1.01      | X2_56 != X0_56
% 3.88/1.01      | sK2 != X1_56 ),
% 3.88/1.01      inference(instantiation,[status(thm)],[c_2458]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3834,plain,
% 3.88/1.01      ( ~ m1_pre_topc(X0_56,sK2)
% 3.88/1.01      | m1_pre_topc(X1_56,sK2)
% 3.88/1.01      | X1_56 != X0_56
% 3.88/1.01      | sK2 != sK2 ),
% 3.88/1.01      inference(instantiation,[status(thm)],[c_3645]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_4323,plain,
% 3.88/1.01      ( m1_pre_topc(X0_56,sK2)
% 3.88/1.01      | ~ m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2)
% 3.88/1.01      | X0_56 != k1_tsep_1(sK2,sK5,sK6)
% 3.88/1.01      | sK2 != sK2 ),
% 3.88/1.01      inference(instantiation,[status(thm)],[c_3834]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_5051,plain,
% 3.88/1.01      ( ~ m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2)
% 3.88/1.01      | m1_pre_topc(sK2,sK2)
% 3.88/1.01      | sK2 != k1_tsep_1(sK2,sK5,sK6)
% 3.88/1.01      | sK2 != sK2 ),
% 3.88/1.01      inference(instantiation,[status(thm)],[c_4323]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_5052,plain,
% 3.88/1.01      ( sK2 != k1_tsep_1(sK2,sK5,sK6)
% 3.88/1.01      | sK2 != sK2
% 3.88/1.01      | m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2) != iProver_top
% 3.88/1.01      | m1_pre_topc(sK2,sK2) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_5051]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_6266,plain,
% 3.88/1.01      ( m1_pre_topc(sK2,sK2) = iProver_top ),
% 3.88/1.01      inference(global_propositional_subsumption,
% 3.88/1.01                [status(thm)],
% 3.88/1.01                [c_5511,c_77,c_79,c_86,c_87,c_88,c_89,c_2417,c_3893,
% 3.88/1.01                 c_3957,c_4391,c_5052]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_68,negated_conjecture,
% 3.88/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 3.88/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2412,negated_conjecture,
% 3.88/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 3.88/1.01      inference(subtyping,[status(esa)],[c_68]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3319,plain,
% 3.88/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_2412]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_8,plain,
% 3.88/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.88/1.01      | ~ m1_pre_topc(X3,X1)
% 3.88/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.88/1.01      | v2_struct_0(X1)
% 3.88/1.01      | v2_struct_0(X2)
% 3.88/1.01      | ~ v2_pre_topc(X2)
% 3.88/1.01      | ~ v2_pre_topc(X1)
% 3.88/1.01      | ~ l1_pre_topc(X1)
% 3.88/1.01      | ~ l1_pre_topc(X2)
% 3.88/1.01      | ~ v1_funct_1(X0)
% 3.88/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.88/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2440,plain,
% 3.88/1.01      ( ~ v1_funct_2(X0_57,u1_struct_0(X0_56),u1_struct_0(X1_56))
% 3.88/1.01      | ~ m1_pre_topc(X2_56,X0_56)
% 3.88/1.01      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 3.88/1.01      | v2_struct_0(X0_56)
% 3.88/1.01      | v2_struct_0(X1_56)
% 3.88/1.01      | ~ v2_pre_topc(X0_56)
% 3.88/1.01      | ~ v2_pre_topc(X1_56)
% 3.88/1.01      | ~ l1_pre_topc(X0_56)
% 3.88/1.01      | ~ l1_pre_topc(X1_56)
% 3.88/1.01      | ~ v1_funct_1(X0_57)
% 3.88/1.01      | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_57,u1_struct_0(X2_56)) = k2_tmap_1(X0_56,X1_56,X0_57,X2_56) ),
% 3.88/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3292,plain,
% 3.88/1.01      ( k2_partfun1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_57,u1_struct_0(X2_56)) = k2_tmap_1(X0_56,X1_56,X0_57,X2_56)
% 3.88/1.01      | v1_funct_2(X0_57,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
% 3.88/1.01      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 3.88/1.01      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
% 3.88/1.01      | v2_struct_0(X1_56) = iProver_top
% 3.88/1.01      | v2_struct_0(X0_56) = iProver_top
% 3.88/1.01      | v2_pre_topc(X1_56) != iProver_top
% 3.88/1.01      | v2_pre_topc(X0_56) != iProver_top
% 3.88/1.01      | l1_pre_topc(X1_56) != iProver_top
% 3.88/1.01      | l1_pre_topc(X0_56) != iProver_top
% 3.88/1.01      | v1_funct_1(X0_57) != iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_2440]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_4586,plain,
% 3.88/1.01      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_56)) = k2_tmap_1(sK2,sK3,sK4,X0_56)
% 3.88/1.01      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | m1_pre_topc(X0_56,sK2) != iProver_top
% 3.88/1.01      | v2_struct_0(sK3) = iProver_top
% 3.88/1.01      | v2_struct_0(sK2) = iProver_top
% 3.88/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.88/1.01      | v2_pre_topc(sK2) != iProver_top
% 3.88/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.88/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.88/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_3319,c_3292]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_75,negated_conjecture,
% 3.88/1.01      ( v2_pre_topc(sK2) ),
% 3.88/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_78,plain,
% 3.88/1.01      ( v2_pre_topc(sK2) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_75]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_73,negated_conjecture,
% 3.88/1.01      ( ~ v2_struct_0(sK3) ),
% 3.88/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_80,plain,
% 3.88/1.01      ( v2_struct_0(sK3) != iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_73]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_72,negated_conjecture,
% 3.88/1.01      ( v2_pre_topc(sK3) ),
% 3.88/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_81,plain,
% 3.88/1.01      ( v2_pre_topc(sK3) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_72]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_71,negated_conjecture,
% 3.88/1.01      ( l1_pre_topc(sK3) ),
% 3.88/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_82,plain,
% 3.88/1.01      ( l1_pre_topc(sK3) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_71]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_70,negated_conjecture,
% 3.88/1.01      ( v1_funct_1(sK4) ),
% 3.88/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_83,plain,
% 3.88/1.01      ( v1_funct_1(sK4) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_70]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_69,negated_conjecture,
% 3.88/1.01      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 3.88/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_84,plain,
% 3.88/1.01      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_69]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_6481,plain,
% 3.88/1.01      ( m1_pre_topc(X0_56,sK2) != iProver_top
% 3.88/1.01      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_56)) = k2_tmap_1(sK2,sK3,sK4,X0_56) ),
% 3.88/1.01      inference(global_propositional_subsumption,
% 3.88/1.01                [status(thm)],
% 3.88/1.01                [c_4586,c_77,c_78,c_79,c_80,c_81,c_82,c_83,c_84]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_6482,plain,
% 3.88/1.01      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_56)) = k2_tmap_1(sK2,sK3,sK4,X0_56)
% 3.88/1.01      | m1_pre_topc(X0_56,sK2) != iProver_top ),
% 3.88/1.01      inference(renaming,[status(thm)],[c_6481]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_5,plain,
% 3.88/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/1.01      | ~ v1_funct_1(X0)
% 3.88/1.01      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.88/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2443,plain,
% 3.88/1.01      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
% 3.88/1.01      | ~ v1_funct_1(X0_57)
% 3.88/1.01      | k2_partfun1(X0_58,X1_58,X0_57,X2_58) = k7_relat_1(X0_57,X2_58) ),
% 3.88/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3289,plain,
% 3.88/1.01      ( k2_partfun1(X0_58,X1_58,X0_57,X2_58) = k7_relat_1(X0_57,X2_58)
% 3.88/1.01      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
% 3.88/1.01      | v1_funct_1(X0_57) != iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_2443]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3874,plain,
% 3.88/1.01      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_58) = k7_relat_1(sK4,X0_58)
% 3.88/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_3319,c_3289]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_5142,plain,
% 3.88/1.01      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_58) = k7_relat_1(sK4,X0_58) ),
% 3.88/1.01      inference(global_propositional_subsumption,
% 3.88/1.01                [status(thm)],
% 3.88/1.01                [c_3874,c_83]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_6487,plain,
% 3.88/1.01      ( k2_tmap_1(sK2,sK3,sK4,X0_56) = k7_relat_1(sK4,u1_struct_0(X0_56))
% 3.88/1.01      | m1_pre_topc(X0_56,sK2) != iProver_top ),
% 3.88/1.01      inference(demodulation,[status(thm)],[c_6482,c_5142]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_6494,plain,
% 3.88/1.01      ( k2_tmap_1(sK2,sK3,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_6266,c_6487]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_18,plain,
% 3.88/1.01      ( ~ sP1(X0,X1,X2,X3,X4)
% 3.88/1.01      | sP0(X4,X3,X2,X1,X0)
% 3.88/1.01      | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
% 3.88/1.01      | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
% 3.88/1.01      | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
% 3.88/1.01      | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
% 3.88/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_28,plain,
% 3.88/1.01      ( sP1(X0,X1,X2,X3,X4)
% 3.88/1.01      | ~ r4_tsep_1(X1,X0,X3)
% 3.88/1.01      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
% 3.88/1.01      | ~ m1_pre_topc(X3,X1)
% 3.88/1.01      | ~ m1_pre_topc(X0,X1)
% 3.88/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 3.88/1.01      | v2_struct_0(X1)
% 3.88/1.01      | v2_struct_0(X4)
% 3.88/1.01      | v2_struct_0(X0)
% 3.88/1.01      | v2_struct_0(X3)
% 3.88/1.01      | ~ v2_pre_topc(X4)
% 3.88/1.01      | ~ v2_pre_topc(X1)
% 3.88/1.01      | ~ l1_pre_topc(X1)
% 3.88/1.01      | ~ l1_pre_topc(X4)
% 3.88/1.01      | ~ v1_funct_1(X2) ),
% 3.88/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_62,negated_conjecture,
% 3.88/1.01      ( r4_tsep_1(sK2,sK5,sK6) ),
% 3.88/1.01      inference(cnf_transformation,[],[f96]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_816,plain,
% 3.88/1.01      ( sP1(X0,X1,X2,X3,X4)
% 3.88/1.01      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
% 3.88/1.01      | ~ m1_pre_topc(X0,X1)
% 3.88/1.01      | ~ m1_pre_topc(X3,X1)
% 3.88/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 3.88/1.01      | v2_struct_0(X1)
% 3.88/1.01      | v2_struct_0(X0)
% 3.88/1.01      | v2_struct_0(X3)
% 3.88/1.01      | v2_struct_0(X4)
% 3.88/1.01      | ~ v2_pre_topc(X1)
% 3.88/1.01      | ~ v2_pre_topc(X4)
% 3.88/1.01      | ~ l1_pre_topc(X1)
% 3.88/1.01      | ~ l1_pre_topc(X4)
% 3.88/1.01      | ~ v1_funct_1(X2)
% 3.88/1.01      | sK5 != X0
% 3.88/1.01      | sK6 != X3
% 3.88/1.01      | sK2 != X1 ),
% 3.88/1.01      inference(resolution_lifted,[status(thm)],[c_28,c_62]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_817,plain,
% 3.88/1.01      ( sP1(sK5,sK2,X0,sK6,X1)
% 3.88/1.01      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 3.88/1.01      | ~ m1_pre_topc(sK5,sK2)
% 3.88/1.01      | ~ m1_pre_topc(sK6,sK2)
% 3.88/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 3.88/1.01      | v2_struct_0(X1)
% 3.88/1.01      | v2_struct_0(sK5)
% 3.88/1.01      | v2_struct_0(sK6)
% 3.88/1.01      | v2_struct_0(sK2)
% 3.88/1.01      | ~ v2_pre_topc(X1)
% 3.88/1.01      | ~ v2_pre_topc(sK2)
% 3.88/1.01      | ~ l1_pre_topc(X1)
% 3.88/1.01      | ~ l1_pre_topc(sK2)
% 3.88/1.01      | ~ v1_funct_1(X0) ),
% 3.88/1.01      inference(unflattening,[status(thm)],[c_816]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_821,plain,
% 3.88/1.01      ( ~ l1_pre_topc(X1)
% 3.88/1.01      | v2_struct_0(X1)
% 3.88/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 3.88/1.01      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 3.88/1.01      | sP1(sK5,sK2,X0,sK6,X1)
% 3.88/1.01      | ~ v2_pre_topc(X1)
% 3.88/1.01      | ~ v1_funct_1(X0) ),
% 3.88/1.01      inference(global_propositional_subsumption,
% 3.88/1.01                [status(thm)],
% 3.88/1.01                [c_817,c_76,c_75,c_74,c_67,c_66,c_65,c_64]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_822,plain,
% 3.88/1.01      ( sP1(sK5,sK2,X0,sK6,X1)
% 3.88/1.01      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 3.88/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 3.88/1.01      | v2_struct_0(X1)
% 3.88/1.01      | ~ v2_pre_topc(X1)
% 3.88/1.01      | ~ l1_pre_topc(X1)
% 3.88/1.01      | ~ v1_funct_1(X0) ),
% 3.88/1.01      inference(renaming,[status(thm)],[c_821]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_857,plain,
% 3.88/1.01      ( sP0(X0,X1,X2,X3,X4)
% 3.88/1.01      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_tsep_1(X3,X4,X1),X0)
% 3.88/1.01      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 3.88/1.01      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))
% 3.88/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 3.88/1.01      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))))
% 3.88/1.01      | v2_struct_0(X6)
% 3.88/1.01      | ~ v2_pre_topc(X6)
% 3.88/1.01      | ~ l1_pre_topc(X6)
% 3.88/1.01      | ~ v1_funct_1(X5)
% 3.88/1.01      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)))
% 3.88/1.01      | X5 != X2
% 3.88/1.01      | X6 != X0
% 3.88/1.01      | sK5 != X4
% 3.88/1.01      | sK6 != X1
% 3.88/1.01      | sK2 != X3 ),
% 3.88/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_822]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_858,plain,
% 3.88/1.01      ( sP0(X0,sK6,X1,sK2,sK5)
% 3.88/1.01      | ~ v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
% 3.88/1.01      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 3.88/1.01      | ~ v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))
% 3.88/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 3.88/1.01      | ~ m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
% 3.88/1.01      | v2_struct_0(X0)
% 3.88/1.01      | ~ v2_pre_topc(X0)
% 3.88/1.01      | ~ l1_pre_topc(X0)
% 3.88/1.01      | ~ v1_funct_1(X1)
% 3.88/1.01      | ~ v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) ),
% 3.88/1.01      inference(unflattening,[status(thm)],[c_857]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2401,plain,
% 3.88/1.01      ( sP0(X0_56,sK6,X0_57,sK2,sK5)
% 3.88/1.01      | ~ v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_56)
% 3.88/1.01      | ~ v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56))
% 3.88/1.01      | ~ v1_funct_2(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_56))
% 3.88/1.01      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56))))
% 3.88/1.01      | ~ m1_subset_1(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_56))))
% 3.88/1.01      | v2_struct_0(X0_56)
% 3.88/1.01      | ~ v2_pre_topc(X0_56)
% 3.88/1.01      | ~ l1_pre_topc(X0_56)
% 3.88/1.01      | ~ v1_funct_1(X0_57)
% 3.88/1.01      | ~ v1_funct_1(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6))) ),
% 3.88/1.01      inference(subtyping,[status(esa)],[c_858]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3330,plain,
% 3.88/1.01      ( sP0(X0_56,sK6,X0_57,sK2,sK5) = iProver_top
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_56) != iProver_top
% 3.88/1.01      | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
% 3.88/1.01      | v1_funct_2(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_56)) != iProver_top
% 3.88/1.01      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56)))) != iProver_top
% 3.88/1.01      | m1_subset_1(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_56)))) != iProver_top
% 3.88/1.01      | v2_struct_0(X0_56) = iProver_top
% 3.88/1.01      | v2_pre_topc(X0_56) != iProver_top
% 3.88/1.01      | l1_pre_topc(X0_56) != iProver_top
% 3.88/1.01      | v1_funct_1(X0_57) != iProver_top
% 3.88/1.01      | v1_funct_1(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6))) != iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_2401]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3339,plain,
% 3.88/1.01      ( sP0(X0_56,sK6,X0_57,sK2,sK5) = iProver_top
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,sK2),sK2,X0_56) != iProver_top
% 3.88/1.01      | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
% 3.88/1.01      | v1_funct_2(k2_tmap_1(sK2,X0_56,X0_57,sK2),u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
% 3.88/1.01      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56)))) != iProver_top
% 3.88/1.01      | m1_subset_1(k2_tmap_1(sK2,X0_56,X0_57,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56)))) != iProver_top
% 3.88/1.01      | v2_struct_0(X0_56) = iProver_top
% 3.88/1.01      | v2_pre_topc(X0_56) != iProver_top
% 3.88/1.01      | l1_pre_topc(X0_56) != iProver_top
% 3.88/1.01      | v1_funct_1(X0_57) != iProver_top
% 3.88/1.01      | v1_funct_1(k2_tmap_1(sK2,X0_56,X0_57,sK2)) != iProver_top ),
% 3.88/1.01      inference(light_normalisation,[status(thm)],[c_3330,c_2417]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_6979,plain,
% 3.88/1.01      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
% 3.88/1.01      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | v2_struct_0(sK3) = iProver_top
% 3.88/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.88/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.88/1.01      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
% 3.88/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_6494,c_3339]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_6982,plain,
% 3.88/1.01      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 3.88/1.01      | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK2)),sK2,sK3) != iProver_top
% 3.88/1.01      | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | v2_struct_0(sK3) = iProver_top
% 3.88/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.88/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.88/1.01      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
% 3.88/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.88/1.01      inference(light_normalisation,[status(thm)],[c_6979,c_6494]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_85,plain,
% 3.88/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_68]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_14,plain,
% 3.88/1.01      ( ~ sP1(X0,X1,X2,X3,X4)
% 3.88/1.01      | ~ sP0(X4,X3,X2,X1,X0)
% 3.88/1.01      | m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) ),
% 3.88/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_986,plain,
% 3.88/1.01      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.88/1.01      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 3.88/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 3.88/1.01      | m1_subset_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))))
% 3.88/1.01      | v2_struct_0(X6)
% 3.88/1.01      | ~ v2_pre_topc(X6)
% 3.88/1.01      | ~ l1_pre_topc(X6)
% 3.88/1.01      | ~ v1_funct_1(X5)
% 3.88/1.01      | X5 != X2
% 3.88/1.01      | X6 != X0
% 3.88/1.01      | sK5 != X4
% 3.88/1.01      | sK6 != X1
% 3.88/1.01      | sK2 != X3 ),
% 3.88/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_822]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_987,plain,
% 3.88/1.01      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 3.88/1.01      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 3.88/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 3.88/1.01      | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
% 3.88/1.01      | v2_struct_0(X0)
% 3.88/1.01      | ~ v2_pre_topc(X0)
% 3.88/1.01      | ~ l1_pre_topc(X0)
% 3.88/1.01      | ~ v1_funct_1(X1) ),
% 3.88/1.01      inference(unflattening,[status(thm)],[c_986]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2397,plain,
% 3.88/1.01      ( ~ sP0(X0_56,sK6,X0_57,sK2,sK5)
% 3.88/1.01      | ~ v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56))
% 3.88/1.01      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56))))
% 3.88/1.01      | m1_subset_1(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_56))))
% 3.88/1.01      | v2_struct_0(X0_56)
% 3.88/1.01      | ~ v2_pre_topc(X0_56)
% 3.88/1.01      | ~ l1_pre_topc(X0_56)
% 3.88/1.01      | ~ v1_funct_1(X0_57) ),
% 3.88/1.01      inference(subtyping,[status(esa)],[c_987]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3334,plain,
% 3.88/1.01      ( sP0(X0_56,sK6,X0_57,sK2,sK5) != iProver_top
% 3.88/1.01      | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
% 3.88/1.01      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56)))) != iProver_top
% 3.88/1.01      | m1_subset_1(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_56)))) = iProver_top
% 3.88/1.01      | v2_struct_0(X0_56) = iProver_top
% 3.88/1.01      | v2_pre_topc(X0_56) != iProver_top
% 3.88/1.01      | l1_pre_topc(X0_56) != iProver_top
% 3.88/1.01      | v1_funct_1(X0_57) != iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_2397]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3338,plain,
% 3.88/1.01      ( sP0(X0_56,sK6,X0_57,sK2,sK5) != iProver_top
% 3.88/1.01      | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
% 3.88/1.01      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56)))) != iProver_top
% 3.88/1.01      | m1_subset_1(k2_tmap_1(sK2,X0_56,X0_57,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56)))) = iProver_top
% 3.88/1.01      | v2_struct_0(X0_56) = iProver_top
% 3.88/1.01      | v2_pre_topc(X0_56) != iProver_top
% 3.88/1.01      | l1_pre_topc(X0_56) != iProver_top
% 3.88/1.01      | v1_funct_1(X0_57) != iProver_top ),
% 3.88/1.01      inference(light_normalisation,[status(thm)],[c_3334,c_2417]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_6980,plain,
% 3.88/1.01      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 3.88/1.01      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top
% 3.88/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | v2_struct_0(sK3) = iProver_top
% 3.88/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.88/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.88/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_6494,c_3338]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_6,plain,
% 3.88/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.88/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_180,plain,
% 3.88/1.01      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_182,plain,
% 3.88/1.01      ( l1_pre_topc(sK3) != iProver_top
% 3.88/1.01      | l1_struct_0(sK3) = iProver_top ),
% 3.88/1.01      inference(instantiation,[status(thm)],[c_180]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2442,plain,
% 3.88/1.01      ( ~ l1_pre_topc(X0_56) | l1_struct_0(X0_56) ),
% 3.88/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3722,plain,
% 3.88/1.01      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 3.88/1.01      inference(instantiation,[status(thm)],[c_2442]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3723,plain,
% 3.88/1.01      ( l1_pre_topc(sK2) != iProver_top
% 3.88/1.01      | l1_struct_0(sK2) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_3722]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_11,plain,
% 3.88/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.88/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.88/1.01      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 3.88/1.01      | ~ l1_struct_0(X3)
% 3.88/1.01      | ~ l1_struct_0(X2)
% 3.88/1.01      | ~ l1_struct_0(X1)
% 3.88/1.01      | ~ v1_funct_1(X0) ),
% 3.88/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2437,plain,
% 3.88/1.01      ( ~ v1_funct_2(X0_57,u1_struct_0(X0_56),u1_struct_0(X1_56))
% 3.88/1.01      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 3.88/1.01      | m1_subset_1(k2_tmap_1(X0_56,X1_56,X0_57,X2_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
% 3.88/1.01      | ~ l1_struct_0(X2_56)
% 3.88/1.01      | ~ l1_struct_0(X1_56)
% 3.88/1.01      | ~ l1_struct_0(X0_56)
% 3.88/1.01      | ~ v1_funct_1(X0_57) ),
% 3.88/1.01      inference(subtyping,[status(esa)],[c_11]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3295,plain,
% 3.88/1.01      ( v1_funct_2(X0_57,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
% 3.88/1.01      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
% 3.88/1.01      | m1_subset_1(k2_tmap_1(X0_56,X1_56,X0_57,X2_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56)))) = iProver_top
% 3.88/1.01      | l1_struct_0(X2_56) != iProver_top
% 3.88/1.01      | l1_struct_0(X1_56) != iProver_top
% 3.88/1.01      | l1_struct_0(X0_56) != iProver_top
% 3.88/1.01      | v1_funct_1(X0_57) != iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_2437]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_8579,plain,
% 3.88/1.01      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top
% 3.88/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | l1_struct_0(sK3) != iProver_top
% 3.88/1.01      | l1_struct_0(sK2) != iProver_top
% 3.88/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_6494,c_3295]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_8973,plain,
% 3.88/1.01      ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 3.88/1.01      inference(global_propositional_subsumption,
% 3.88/1.01                [status(thm)],
% 3.88/1.01                [c_6980,c_79,c_82,c_83,c_84,c_85,c_182,c_3723,c_8579]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_15,plain,
% 3.88/1.01      ( ~ sP1(X0,X1,X2,X3,X4)
% 3.88/1.01      | ~ sP0(X4,X3,X2,X1,X0)
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) ),
% 3.88/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_956,plain,
% 3.88/1.01      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_tsep_1(X3,X4,X1),X0)
% 3.88/1.01      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 3.88/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 3.88/1.01      | v2_struct_0(X6)
% 3.88/1.01      | ~ v2_pre_topc(X6)
% 3.88/1.01      | ~ l1_pre_topc(X6)
% 3.88/1.01      | ~ v1_funct_1(X5)
% 3.88/1.01      | X5 != X2
% 3.88/1.01      | X6 != X0
% 3.88/1.01      | sK5 != X4
% 3.88/1.01      | sK6 != X1
% 3.88/1.01      | sK2 != X3 ),
% 3.88/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_822]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_957,plain,
% 3.88/1.01      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
% 3.88/1.01      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 3.88/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 3.88/1.01      | v2_struct_0(X0)
% 3.88/1.01      | ~ v2_pre_topc(X0)
% 3.88/1.01      | ~ l1_pre_topc(X0)
% 3.88/1.01      | ~ v1_funct_1(X1) ),
% 3.88/1.01      inference(unflattening,[status(thm)],[c_956]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2398,plain,
% 3.88/1.01      ( ~ sP0(X0_56,sK6,X0_57,sK2,sK5)
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_56)
% 3.88/1.01      | ~ v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56))
% 3.88/1.01      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56))))
% 3.88/1.01      | v2_struct_0(X0_56)
% 3.88/1.01      | ~ v2_pre_topc(X0_56)
% 3.88/1.01      | ~ l1_pre_topc(X0_56)
% 3.88/1.01      | ~ v1_funct_1(X0_57) ),
% 3.88/1.01      inference(subtyping,[status(esa)],[c_957]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3333,plain,
% 3.88/1.01      ( sP0(X0_56,sK6,X0_57,sK2,sK5) != iProver_top
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_56) = iProver_top
% 3.88/1.01      | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
% 3.88/1.01      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56)))) != iProver_top
% 3.88/1.01      | v2_struct_0(X0_56) = iProver_top
% 3.88/1.01      | v2_pre_topc(X0_56) != iProver_top
% 3.88/1.01      | l1_pre_topc(X0_56) != iProver_top
% 3.88/1.01      | v1_funct_1(X0_57) != iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_2398]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3336,plain,
% 3.88/1.01      ( sP0(X0_56,sK6,X0_57,sK2,sK5) != iProver_top
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,sK2),sK2,X0_56) = iProver_top
% 3.88/1.01      | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
% 3.88/1.01      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56)))) != iProver_top
% 3.88/1.01      | v2_struct_0(X0_56) = iProver_top
% 3.88/1.01      | v2_pre_topc(X0_56) != iProver_top
% 3.88/1.01      | l1_pre_topc(X0_56) != iProver_top
% 3.88/1.01      | v1_funct_1(X0_57) != iProver_top ),
% 3.88/1.01      inference(light_normalisation,[status(thm)],[c_3333,c_2417]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_8977,plain,
% 3.88/1.01      ( sP0(sK3,sK6,k7_relat_1(sK4,u1_struct_0(sK2)),sK2,sK5) != iProver_top
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(sK2,sK3,k7_relat_1(sK4,u1_struct_0(sK2)),sK2),sK2,sK3) = iProver_top
% 3.88/1.01      | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | v2_struct_0(sK3) = iProver_top
% 3.88/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.88/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.88/1.01      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_8973,c_3336]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_12,plain,
% 3.88/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.88/1.01      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 3.88/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.88/1.01      | ~ l1_struct_0(X3)
% 3.88/1.01      | ~ l1_struct_0(X2)
% 3.88/1.01      | ~ l1_struct_0(X1)
% 3.88/1.01      | ~ v1_funct_1(X0) ),
% 3.88/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2436,plain,
% 3.88/1.01      ( ~ v1_funct_2(X0_57,u1_struct_0(X0_56),u1_struct_0(X1_56))
% 3.88/1.01      | v1_funct_2(k2_tmap_1(X0_56,X1_56,X0_57,X2_56),u1_struct_0(X2_56),u1_struct_0(X1_56))
% 3.88/1.01      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 3.88/1.01      | ~ l1_struct_0(X2_56)
% 3.88/1.01      | ~ l1_struct_0(X1_56)
% 3.88/1.01      | ~ l1_struct_0(X0_56)
% 3.88/1.01      | ~ v1_funct_1(X0_57) ),
% 3.88/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3296,plain,
% 3.88/1.01      ( v1_funct_2(X0_57,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
% 3.88/1.01      | v1_funct_2(k2_tmap_1(X0_56,X1_56,X0_57,X2_56),u1_struct_0(X2_56),u1_struct_0(X1_56)) = iProver_top
% 3.88/1.01      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
% 3.88/1.01      | l1_struct_0(X2_56) != iProver_top
% 3.88/1.01      | l1_struct_0(X1_56) != iProver_top
% 3.88/1.01      | l1_struct_0(X0_56) != iProver_top
% 3.88/1.01      | v1_funct_1(X0_57) != iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_2436]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_8710,plain,
% 3.88/1.01      ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
% 3.88/1.01      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | l1_struct_0(sK3) != iProver_top
% 3.88/1.01      | l1_struct_0(sK2) != iProver_top
% 3.88/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_6494,c_3296]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_13,plain,
% 3.88/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.88/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.88/1.01      | ~ l1_struct_0(X3)
% 3.88/1.01      | ~ l1_struct_0(X2)
% 3.88/1.01      | ~ l1_struct_0(X1)
% 3.88/1.01      | ~ v1_funct_1(X0)
% 3.88/1.01      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 3.88/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2435,plain,
% 3.88/1.01      ( ~ v1_funct_2(X0_57,u1_struct_0(X0_56),u1_struct_0(X1_56))
% 3.88/1.01      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 3.88/1.01      | ~ l1_struct_0(X2_56)
% 3.88/1.01      | ~ l1_struct_0(X1_56)
% 3.88/1.01      | ~ l1_struct_0(X0_56)
% 3.88/1.01      | ~ v1_funct_1(X0_57)
% 3.88/1.01      | v1_funct_1(k2_tmap_1(X0_56,X1_56,X0_57,X2_56)) ),
% 3.88/1.01      inference(subtyping,[status(esa)],[c_13]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3297,plain,
% 3.88/1.01      ( v1_funct_2(X0_57,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
% 3.88/1.01      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
% 3.88/1.01      | l1_struct_0(X2_56) != iProver_top
% 3.88/1.01      | l1_struct_0(X1_56) != iProver_top
% 3.88/1.01      | l1_struct_0(X0_56) != iProver_top
% 3.88/1.01      | v1_funct_1(X0_57) != iProver_top
% 3.88/1.01      | v1_funct_1(k2_tmap_1(X0_56,X1_56,X0_57,X2_56)) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_2435]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_8604,plain,
% 3.88/1.01      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | l1_struct_0(X0_56) != iProver_top
% 3.88/1.01      | l1_struct_0(sK3) != iProver_top
% 3.88/1.01      | l1_struct_0(sK2) != iProver_top
% 3.88/1.01      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_56)) = iProver_top
% 3.88/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_3319,c_3297]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_8828,plain,
% 3.88/1.01      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_56)) = iProver_top
% 3.88/1.01      | l1_struct_0(X0_56) != iProver_top ),
% 3.88/1.01      inference(global_propositional_subsumption,
% 3.88/1.01                [status(thm)],
% 3.88/1.01                [c_8604,c_79,c_82,c_83,c_84,c_182,c_3723]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_8829,plain,
% 3.88/1.01      ( l1_struct_0(X0_56) != iProver_top
% 3.88/1.01      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_56)) = iProver_top ),
% 3.88/1.01      inference(renaming,[status(thm)],[c_8828]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_8836,plain,
% 3.88/1.01      ( l1_struct_0(sK2) != iProver_top
% 3.88/1.01      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_6494,c_8829]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_9146,plain,
% 3.88/1.01      ( v5_pre_topc(k2_tmap_1(sK2,sK3,k7_relat_1(sK4,u1_struct_0(sK2)),sK2),sK2,sK3) = iProver_top
% 3.88/1.01      | sP0(sK3,sK6,k7_relat_1(sK4,u1_struct_0(sK2)),sK2,sK5) != iProver_top ),
% 3.88/1.01      inference(global_propositional_subsumption,
% 3.88/1.01                [status(thm)],
% 3.88/1.01                [c_8977,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_182,c_3723,
% 3.88/1.01                 c_8710,c_8836]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_9147,plain,
% 3.88/1.01      ( sP0(sK3,sK6,k7_relat_1(sK4,u1_struct_0(sK2)),sK2,sK5) != iProver_top
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(sK2,sK3,k7_relat_1(sK4,u1_struct_0(sK2)),sK2),sK2,sK3) = iProver_top ),
% 3.88/1.01      inference(renaming,[status(thm)],[c_9146]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_4,plain,
% 3.88/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/1.01      | v4_relat_1(X0,X1) ),
% 3.88/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_1,plain,
% 3.88/1.01      ( r1_tarski(k1_relat_1(X0),X1)
% 3.88/1.01      | ~ v4_relat_1(X0,X1)
% 3.88/1.01      | ~ v1_relat_1(X0) ),
% 3.88/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_775,plain,
% 3.88/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/1.01      | r1_tarski(k1_relat_1(X0),X1)
% 3.88/1.01      | ~ v1_relat_1(X0) ),
% 3.88/1.01      inference(resolution,[status(thm)],[c_4,c_1]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3,plain,
% 3.88/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/1.01      | v1_relat_1(X0) ),
% 3.88/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_779,plain,
% 3.88/1.01      ( r1_tarski(k1_relat_1(X0),X1)
% 3.88/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.88/1.01      inference(global_propositional_subsumption,
% 3.88/1.01                [status(thm)],
% 3.88/1.01                [c_775,c_3]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_780,plain,
% 3.88/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/1.01      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.88/1.01      inference(renaming,[status(thm)],[c_779]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2,plain,
% 3.88/1.01      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.88/1.01      | ~ v1_relat_1(X0)
% 3.88/1.01      | k7_relat_1(X0,X1) = X0 ),
% 3.88/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_796,plain,
% 3.88/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/1.01      | ~ v1_relat_1(X0)
% 3.88/1.01      | k7_relat_1(X0,X1) = X0 ),
% 3.88/1.01      inference(resolution,[status(thm)],[c_780,c_2]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_800,plain,
% 3.88/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/1.01      | k7_relat_1(X0,X1) = X0 ),
% 3.88/1.01      inference(global_propositional_subsumption,
% 3.88/1.01                [status(thm)],
% 3.88/1.01                [c_796,c_3]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2402,plain,
% 3.88/1.01      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
% 3.88/1.01      | k7_relat_1(X0_57,X0_58) = X0_57 ),
% 3.88/1.01      inference(subtyping,[status(esa)],[c_800]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3329,plain,
% 3.88/1.01      ( k7_relat_1(X0_57,X0_58) = X0_57
% 3.88/1.01      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_2402]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_9029,plain,
% 3.88/1.01      ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK4 ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_3319,c_3329]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_9079,plain,
% 3.88/1.01      ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4 ),
% 3.88/1.01      inference(demodulation,[status(thm)],[c_9029,c_6494]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_9150,plain,
% 3.88/1.01      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 3.88/1.01      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 3.88/1.01      inference(light_normalisation,[status(thm)],[c_9147,c_9029,c_9079]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_55,negated_conjecture,
% 3.88/1.01      ( v5_pre_topc(sK4,sK2,sK3)
% 3.88/1.01      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 3.88/1.01      inference(cnf_transformation,[],[f103]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_97,plain,
% 3.88/1.01      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 3.88/1.01      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_51,negated_conjecture,
% 3.88/1.01      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 3.88/1.01      | v5_pre_topc(sK4,sK2,sK3) ),
% 3.88/1.01      inference(cnf_transformation,[],[f107]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_101,plain,
% 3.88/1.01      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
% 3.88/1.01      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_47,negated_conjecture,
% 3.88/1.01      ( v5_pre_topc(sK4,sK2,sK3)
% 3.88/1.01      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 3.88/1.01      inference(cnf_transformation,[],[f111]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_105,plain,
% 3.88/1.01      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 3.88/1.01      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_39,negated_conjecture,
% 3.88/1.01      ( v5_pre_topc(sK4,sK2,sK3)
% 3.88/1.01      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
% 3.88/1.01      inference(cnf_transformation,[],[f119]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_113,plain,
% 3.88/1.01      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 3.88/1.01      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_35,negated_conjecture,
% 3.88/1.01      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 3.88/1.01      | v5_pre_topc(sK4,sK2,sK3) ),
% 3.88/1.01      inference(cnf_transformation,[],[f123]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_117,plain,
% 3.88/1.01      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
% 3.88/1.01      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_31,negated_conjecture,
% 3.88/1.01      ( v5_pre_topc(sK4,sK2,sK3)
% 3.88/1.01      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 3.88/1.01      inference(cnf_transformation,[],[f127]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_121,plain,
% 3.88/1.01      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 3.88/1.01      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3438,plain,
% 3.88/1.01      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.88/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.88/1.01      | ~ l1_struct_0(sK5)
% 3.88/1.01      | ~ l1_struct_0(sK3)
% 3.88/1.01      | ~ l1_struct_0(sK2)
% 3.88/1.01      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 3.88/1.01      | ~ v1_funct_1(sK4) ),
% 3.88/1.01      inference(instantiation,[status(thm)],[c_2435]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3439,plain,
% 3.88/1.01      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | l1_struct_0(sK5) != iProver_top
% 3.88/1.01      | l1_struct_0(sK3) != iProver_top
% 3.88/1.01      | l1_struct_0(sK2) != iProver_top
% 3.88/1.01      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top
% 3.88/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_3438]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_19,plain,
% 3.88/1.01      ( sP0(X0,X1,X2,X3,X4)
% 3.88/1.01      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
% 3.88/1.01      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
% 3.88/1.01      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
% 3.88/1.01      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
% 3.88/1.01      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 3.88/1.01      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
% 3.88/1.01      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
% 3.88/1.01      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
% 3.88/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2434,plain,
% 3.88/1.01      ( sP0(X0_56,X1_56,X0_57,X2_56,X3_56)
% 3.88/1.01      | ~ v5_pre_topc(k2_tmap_1(X2_56,X0_56,X0_57,X1_56),X1_56,X0_56)
% 3.88/1.01      | ~ v5_pre_topc(k2_tmap_1(X2_56,X0_56,X0_57,X3_56),X3_56,X0_56)
% 3.88/1.01      | ~ v1_funct_2(k2_tmap_1(X2_56,X0_56,X0_57,X1_56),u1_struct_0(X1_56),u1_struct_0(X0_56))
% 3.88/1.01      | ~ v1_funct_2(k2_tmap_1(X2_56,X0_56,X0_57,X3_56),u1_struct_0(X3_56),u1_struct_0(X0_56))
% 3.88/1.01      | ~ m1_subset_1(k2_tmap_1(X2_56,X0_56,X0_57,X1_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(X0_56))))
% 3.88/1.01      | ~ m1_subset_1(k2_tmap_1(X2_56,X0_56,X0_57,X3_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_56),u1_struct_0(X0_56))))
% 3.88/1.01      | ~ v1_funct_1(k2_tmap_1(X2_56,X0_56,X0_57,X1_56))
% 3.88/1.01      | ~ v1_funct_1(k2_tmap_1(X2_56,X0_56,X0_57,X3_56)) ),
% 3.88/1.01      inference(subtyping,[status(esa)],[c_19]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3510,plain,
% 3.88/1.01      ( sP0(X0_56,sK6,X0_57,sK2,sK5)
% 3.88/1.01      | ~ v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,sK5),sK5,X0_56)
% 3.88/1.01      | ~ v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,sK6),sK6,X0_56)
% 3.88/1.01      | ~ v1_funct_2(k2_tmap_1(sK2,X0_56,X0_57,sK5),u1_struct_0(sK5),u1_struct_0(X0_56))
% 3.88/1.01      | ~ v1_funct_2(k2_tmap_1(sK2,X0_56,X0_57,sK6),u1_struct_0(sK6),u1_struct_0(X0_56))
% 3.88/1.01      | ~ m1_subset_1(k2_tmap_1(sK2,X0_56,X0_57,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_56))))
% 3.88/1.01      | ~ m1_subset_1(k2_tmap_1(sK2,X0_56,X0_57,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_56))))
% 3.88/1.01      | ~ v1_funct_1(k2_tmap_1(sK2,X0_56,X0_57,sK5))
% 3.88/1.01      | ~ v1_funct_1(k2_tmap_1(sK2,X0_56,X0_57,sK6)) ),
% 3.88/1.01      inference(instantiation,[status(thm)],[c_2434]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3511,plain,
% 3.88/1.01      ( sP0(X0_56,sK6,X0_57,sK2,sK5) = iProver_top
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,sK5),sK5,X0_56) != iProver_top
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,sK6),sK6,X0_56) != iProver_top
% 3.88/1.01      | v1_funct_2(k2_tmap_1(sK2,X0_56,X0_57,sK5),u1_struct_0(sK5),u1_struct_0(X0_56)) != iProver_top
% 3.88/1.01      | v1_funct_2(k2_tmap_1(sK2,X0_56,X0_57,sK6),u1_struct_0(sK6),u1_struct_0(X0_56)) != iProver_top
% 3.88/1.01      | m1_subset_1(k2_tmap_1(sK2,X0_56,X0_57,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_56)))) != iProver_top
% 3.88/1.01      | m1_subset_1(k2_tmap_1(sK2,X0_56,X0_57,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_56)))) != iProver_top
% 3.88/1.01      | v1_funct_1(k2_tmap_1(sK2,X0_56,X0_57,sK5)) != iProver_top
% 3.88/1.01      | v1_funct_1(k2_tmap_1(sK2,X0_56,X0_57,sK6)) != iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_3510]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3513,plain,
% 3.88/1.01      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 3.88/1.01      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 3.88/1.01      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 3.88/1.01      inference(instantiation,[status(thm)],[c_3511]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3546,plain,
% 3.88/1.01      ( ~ l1_pre_topc(sK5) | l1_struct_0(sK5) ),
% 3.88/1.01      inference(instantiation,[status(thm)],[c_2442]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3547,plain,
% 3.88/1.01      ( l1_pre_topc(sK5) != iProver_top
% 3.88/1.01      | l1_struct_0(sK5) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_3546]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_7,plain,
% 3.88/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.88/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2441,plain,
% 3.88/1.01      ( ~ m1_pre_topc(X0_56,X1_56)
% 3.88/1.01      | ~ l1_pre_topc(X1_56)
% 3.88/1.01      | l1_pre_topc(X0_56) ),
% 3.88/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3663,plain,
% 3.88/1.01      ( ~ m1_pre_topc(sK5,X0_56)
% 3.88/1.01      | ~ l1_pre_topc(X0_56)
% 3.88/1.01      | l1_pre_topc(sK5) ),
% 3.88/1.01      inference(instantiation,[status(thm)],[c_2441]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3941,plain,
% 3.88/1.01      ( ~ m1_pre_topc(sK5,sK2) | l1_pre_topc(sK5) | ~ l1_pre_topc(sK2) ),
% 3.88/1.01      inference(instantiation,[status(thm)],[c_3663]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3942,plain,
% 3.88/1.01      ( m1_pre_topc(sK5,sK2) != iProver_top
% 3.88/1.01      | l1_pre_topc(sK5) = iProver_top
% 3.88/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_3941]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2416,negated_conjecture,
% 3.88/1.01      ( m1_pre_topc(sK6,sK2) ),
% 3.88/1.01      inference(subtyping,[status(esa)],[c_64]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3315,plain,
% 3.88/1.01      ( m1_pre_topc(sK6,sK2) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_2416]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3291,plain,
% 3.88/1.01      ( m1_pre_topc(X0_56,X1_56) != iProver_top
% 3.88/1.01      | l1_pre_topc(X1_56) != iProver_top
% 3.88/1.01      | l1_pre_topc(X0_56) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_2441]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_4012,plain,
% 3.88/1.01      ( l1_pre_topc(sK6) = iProver_top
% 3.88/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_3315,c_3291]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_5022,plain,
% 3.88/1.01      ( l1_pre_topc(sK6) = iProver_top ),
% 3.88/1.01      inference(global_propositional_subsumption,
% 3.88/1.01                [status(thm)],
% 3.88/1.01                [c_4012,c_79]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3290,plain,
% 3.88/1.01      ( l1_pre_topc(X0_56) != iProver_top
% 3.88/1.01      | l1_struct_0(X0_56) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_2442]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_5026,plain,
% 3.88/1.01      ( l1_struct_0(sK6) = iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_5022,c_3290]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_5545,plain,
% 3.88/1.01      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.88/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.88/1.01      | ~ l1_struct_0(X0_56)
% 3.88/1.01      | ~ l1_struct_0(sK3)
% 3.88/1.01      | ~ l1_struct_0(sK2)
% 3.88/1.01      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_56))
% 3.88/1.01      | ~ v1_funct_1(sK4) ),
% 3.88/1.01      inference(instantiation,[status(thm)],[c_2435]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_6448,plain,
% 3.88/1.01      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.88/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.88/1.01      | ~ l1_struct_0(sK6)
% 3.88/1.01      | ~ l1_struct_0(sK3)
% 3.88/1.01      | ~ l1_struct_0(sK2)
% 3.88/1.01      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 3.88/1.01      | ~ v1_funct_1(sK4) ),
% 3.88/1.01      inference(instantiation,[status(thm)],[c_5545]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_6449,plain,
% 3.88/1.01      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | l1_struct_0(sK6) != iProver_top
% 3.88/1.01      | l1_struct_0(sK3) != iProver_top
% 3.88/1.01      | l1_struct_0(sK2) != iProver_top
% 3.88/1.01      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top
% 3.88/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_6448]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_9152,plain,
% 3.88/1.01      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 3.88/1.01      inference(global_propositional_subsumption,
% 3.88/1.01                [status(thm)],
% 3.88/1.01                [c_9150,c_79,c_82,c_83,c_84,c_85,c_87,c_97,c_101,c_105,
% 3.88/1.01                 c_113,c_117,c_121,c_182,c_3439,c_3513,c_3547,c_3723,
% 3.88/1.01                 c_3942,c_5026,c_6449]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_8584,plain,
% 3.88/1.01      ( sP0(X0_56,sK6,X0_57,sK2,sK5) = iProver_top
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,sK2),sK2,X0_56) != iProver_top
% 3.88/1.01      | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
% 3.88/1.01      | v1_funct_2(k2_tmap_1(sK2,X0_56,X0_57,sK2),u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
% 3.88/1.01      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56)))) != iProver_top
% 3.88/1.01      | v2_struct_0(X0_56) = iProver_top
% 3.88/1.01      | v2_pre_topc(X0_56) != iProver_top
% 3.88/1.01      | l1_pre_topc(X0_56) != iProver_top
% 3.88/1.01      | l1_struct_0(X0_56) != iProver_top
% 3.88/1.01      | l1_struct_0(sK2) != iProver_top
% 3.88/1.01      | v1_funct_1(X0_57) != iProver_top
% 3.88/1.01      | v1_funct_1(k2_tmap_1(sK2,X0_56,X0_57,sK2)) != iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_3295,c_3339]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2491,plain,
% 3.88/1.01      ( l1_pre_topc(X0_56) != iProver_top
% 3.88/1.01      | l1_struct_0(X0_56) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_2442]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_9225,plain,
% 3.88/1.01      ( sP0(X0_56,sK6,X0_57,sK2,sK5) = iProver_top
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(sK2,X0_56,X0_57,sK2),sK2,X0_56) != iProver_top
% 3.88/1.01      | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
% 3.88/1.01      | v1_funct_2(k2_tmap_1(sK2,X0_56,X0_57,sK2),u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
% 3.88/1.01      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56)))) != iProver_top
% 3.88/1.01      | v2_struct_0(X0_56) = iProver_top
% 3.88/1.01      | v2_pre_topc(X0_56) != iProver_top
% 3.88/1.01      | l1_pre_topc(X0_56) != iProver_top
% 3.88/1.01      | v1_funct_1(X0_57) != iProver_top
% 3.88/1.01      | v1_funct_1(k2_tmap_1(sK2,X0_56,X0_57,sK2)) != iProver_top ),
% 3.88/1.01      inference(global_propositional_subsumption,
% 3.88/1.01                [status(thm)],
% 3.88/1.01                [c_8584,c_79,c_2491,c_3723]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_10253,plain,
% 3.88/1.01      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
% 3.88/1.01      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | v2_struct_0(sK3) = iProver_top
% 3.88/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.88/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.88/1.01      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
% 3.88/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_9079,c_9225]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_10263,plain,
% 3.88/1.01      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 3.88/1.01      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 3.88/1.01      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | v2_struct_0(sK3) = iProver_top
% 3.88/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.88/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.88/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.88/1.01      inference(light_normalisation,[status(thm)],[c_10253,c_9079]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_11076,plain,
% 3.88/1.01      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top ),
% 3.88/1.01      inference(global_propositional_subsumption,
% 3.88/1.01                [status(thm)],
% 3.88/1.01                [c_6982,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_87,c_97,
% 3.88/1.01                 c_101,c_105,c_113,c_117,c_121,c_182,c_3439,c_3513,
% 3.88/1.01                 c_3547,c_3723,c_3942,c_5026,c_6449,c_9150,c_10263]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_25,plain,
% 3.88/1.01      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) ),
% 3.88/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2428,plain,
% 3.88/1.01      ( ~ sP0(X0_56,X1_56,X0_57,X2_56,X3_56)
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(X2_56,X0_56,X0_57,X3_56),X3_56,X0_56) ),
% 3.88/1.01      inference(subtyping,[status(esa)],[c_25]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3304,plain,
% 3.88/1.01      ( sP0(X0_56,X1_56,X0_57,X2_56,X3_56) != iProver_top
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(X2_56,X0_56,X0_57,X3_56),X3_56,X0_56) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_2428]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_11084,plain,
% 3.88/1.01      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_11076,c_3304]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2414,negated_conjecture,
% 3.88/1.01      ( m1_pre_topc(sK5,sK2) ),
% 3.88/1.01      inference(subtyping,[status(esa)],[c_66]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3317,plain,
% 3.88/1.01      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_2414]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_6492,plain,
% 3.88/1.01      ( k2_tmap_1(sK2,sK3,sK4,sK5) = k7_relat_1(sK4,u1_struct_0(sK5)) ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_3317,c_6487]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_11091,plain,
% 3.88/1.01      ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) = iProver_top ),
% 3.88/1.01      inference(light_normalisation,[status(thm)],[c_11084,c_6492]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_21,plain,
% 3.88/1.01      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) ),
% 3.88/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2432,plain,
% 3.88/1.01      ( ~ sP0(X0_56,X1_56,X0_57,X2_56,X3_56)
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(X2_56,X0_56,X0_57,X1_56),X1_56,X0_56) ),
% 3.88/1.01      inference(subtyping,[status(esa)],[c_21]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3300,plain,
% 3.88/1.01      ( sP0(X0_56,X1_56,X0_57,X2_56,X3_56) != iProver_top
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(X2_56,X0_56,X0_57,X1_56),X1_56,X0_56) = iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_2432]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_11085,plain,
% 3.88/1.01      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_11076,c_3300]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_6491,plain,
% 3.88/1.01      ( k2_tmap_1(sK2,sK3,sK4,sK6) = k7_relat_1(sK4,u1_struct_0(sK6)) ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_3315,c_6487]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_11090,plain,
% 3.88/1.01      ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) = iProver_top ),
% 3.88/1.01      inference(light_normalisation,[status(thm)],[c_11085,c_6491]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_29,negated_conjecture,
% 3.88/1.01      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 3.88/1.01      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 3.88/1.01      | ~ v5_pre_topc(sK4,sK2,sK3)
% 3.88/1.01      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.88/1.01      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 3.88/1.01      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.88/1.01      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.88/1.01      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 3.88/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.88/1.01      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 3.88/1.01      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 3.88/1.01      | ~ v1_funct_1(sK4) ),
% 3.88/1.01      inference(cnf_transformation,[],[f129]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_496,plain,
% 3.88/1.01      ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 3.88/1.01      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 3.88/1.01      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 3.88/1.01      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.88/1.01      | ~ v5_pre_topc(sK4,sK2,sK3)
% 3.88/1.01      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 3.88/1.01      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 3.88/1.01      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.88/1.01      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 3.88/1.01      inference(global_propositional_subsumption,
% 3.88/1.01                [status(thm)],
% 3.88/1.01                [c_29,c_70,c_69,c_68]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_497,negated_conjecture,
% 3.88/1.01      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 3.88/1.01      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 3.88/1.01      | ~ v5_pre_topc(sK4,sK2,sK3)
% 3.88/1.01      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.88/1.01      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 3.88/1.01      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.88/1.01      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 3.88/1.01      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 3.88/1.01      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 3.88/1.01      inference(renaming,[status(thm)],[c_496]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_2403,negated_conjecture,
% 3.88/1.01      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 3.88/1.01      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 3.88/1.01      | ~ v5_pre_topc(sK4,sK2,sK3)
% 3.88/1.01      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.88/1.01      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 3.88/1.01      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.88/1.01      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 3.88/1.01      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 3.88/1.01      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 3.88/1.01      inference(subtyping,[status(esa)],[c_497]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_3328,plain,
% 3.88/1.01      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 3.88/1.01      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 3.88/1.01      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 3.88/1.01      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 3.88/1.01      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 3.88/1.01      inference(predicate_to_equality,[status(thm)],[c_2403]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_6503,plain,
% 3.88/1.01      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 3.88/1.01      | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) != iProver_top
% 3.88/1.01      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 3.88/1.01      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 3.88/1.01      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) != iProver_top ),
% 3.88/1.01      inference(demodulation,[status(thm)],[c_6491,c_3328]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_6504,plain,
% 3.88/1.01      ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) != iProver_top
% 3.88/1.01      | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) != iProver_top
% 3.88/1.01      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 3.88/1.01      | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK5))) != iProver_top
% 3.88/1.01      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) != iProver_top ),
% 3.88/1.01      inference(light_normalisation,[status(thm)],[c_6503,c_6492]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_8577,plain,
% 3.88/1.01      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top
% 3.88/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | l1_struct_0(sK6) != iProver_top
% 3.88/1.01      | l1_struct_0(sK3) != iProver_top
% 3.88/1.01      | l1_struct_0(sK2) != iProver_top
% 3.88/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_6491,c_3295]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_8578,plain,
% 3.88/1.01      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top
% 3.88/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | l1_struct_0(sK5) != iProver_top
% 3.88/1.01      | l1_struct_0(sK3) != iProver_top
% 3.88/1.01      | l1_struct_0(sK2) != iProver_top
% 3.88/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_6492,c_3295]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_8708,plain,
% 3.88/1.01      ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top
% 3.88/1.01      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | l1_struct_0(sK6) != iProver_top
% 3.88/1.01      | l1_struct_0(sK3) != iProver_top
% 3.88/1.01      | l1_struct_0(sK2) != iProver_top
% 3.88/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_6491,c_3296]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_8709,plain,
% 3.88/1.01      ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
% 3.88/1.01      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.88/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.88/1.01      | l1_struct_0(sK5) != iProver_top
% 3.88/1.01      | l1_struct_0(sK3) != iProver_top
% 3.88/1.01      | l1_struct_0(sK2) != iProver_top
% 3.88/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_6492,c_3296]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_8834,plain,
% 3.88/1.01      ( l1_struct_0(sK6) != iProver_top
% 3.88/1.01      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) = iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_6491,c_8829]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_8835,plain,
% 3.88/1.01      ( l1_struct_0(sK5) != iProver_top
% 3.88/1.01      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK5))) = iProver_top ),
% 3.88/1.01      inference(superposition,[status(thm)],[c_6492,c_8829]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_10356,plain,
% 3.88/1.01      ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) != iProver_top
% 3.88/1.01      | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) != iProver_top ),
% 3.88/1.01      inference(global_propositional_subsumption,
% 3.88/1.01                [status(thm)],
% 3.88/1.01                [c_6504,c_79,c_82,c_83,c_84,c_85,c_87,c_97,c_101,c_105,
% 3.88/1.01                 c_113,c_117,c_121,c_182,c_3439,c_3513,c_3547,c_3723,
% 3.88/1.01                 c_3942,c_5026,c_6449,c_8577,c_8578,c_8708,c_8709,c_8834,
% 3.88/1.01                 c_8835,c_9150]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(c_10357,plain,
% 3.88/1.01      ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) != iProver_top
% 3.88/1.01      | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) != iProver_top ),
% 3.88/1.01      inference(renaming,[status(thm)],[c_10356]) ).
% 3.88/1.01  
% 3.88/1.01  cnf(contradiction,plain,
% 3.88/1.01      ( $false ),
% 3.88/1.01      inference(minisat,[status(thm)],[c_11091,c_11090,c_10357]) ).
% 3.88/1.01  
% 3.88/1.01  
% 3.88/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.88/1.01  
% 3.88/1.01  ------                               Statistics
% 3.88/1.01  
% 3.88/1.01  ------ General
% 3.88/1.01  
% 3.88/1.01  abstr_ref_over_cycles:                  0
% 3.88/1.01  abstr_ref_under_cycles:                 0
% 3.88/1.01  gc_basic_clause_elim:                   0
% 3.88/1.01  forced_gc_time:                         0
% 3.88/1.01  parsing_time:                           0.013
% 3.88/1.01  unif_index_cands_time:                  0.
% 3.88/1.01  unif_index_add_time:                    0.
% 3.88/1.01  orderings_time:                         0.
% 3.88/1.01  out_proof_time:                         0.025
% 3.88/1.01  total_time:                             0.465
% 3.88/1.01  num_of_symbols:                         61
% 3.88/1.01  num_of_terms:                           11160
% 3.88/1.01  
% 3.88/1.01  ------ Preprocessing
% 3.88/1.01  
% 3.88/1.01  num_of_splits:                          0
% 3.88/1.01  num_of_split_atoms:                     0
% 3.88/1.01  num_of_reused_defs:                     0
% 3.88/1.01  num_eq_ax_congr_red:                    31
% 3.88/1.01  num_of_sem_filtered_clauses:            1
% 3.88/1.01  num_of_subtypes:                        5
% 3.88/1.01  monotx_restored_types:                  0
% 3.88/1.01  sat_num_of_epr_types:                   0
% 3.88/1.01  sat_num_of_non_cyclic_types:            0
% 3.88/1.01  sat_guarded_non_collapsed_types:        1
% 3.88/1.01  num_pure_diseq_elim:                    0
% 3.88/1.01  simp_replaced_by:                       0
% 3.88/1.01  res_preprocessed:                       239
% 3.88/1.01  prep_upred:                             0
% 3.88/1.01  prep_unflattend:                        148
% 3.88/1.01  smt_new_axioms:                         0
% 3.88/1.01  pred_elim_cands:                        10
% 3.88/1.01  pred_elim:                              5
% 3.88/1.01  pred_elim_cl:                           6
% 3.88/1.01  pred_elim_cycles:                       7
% 3.88/1.01  merged_defs:                            0
% 3.88/1.01  merged_defs_ncl:                        0
% 3.88/1.01  bin_hyper_res:                          0
% 3.88/1.01  prep_cycles:                            4
% 3.88/1.01  pred_elim_time:                         0.06
% 3.88/1.01  splitting_time:                         0.
% 3.88/1.01  sem_filter_time:                        0.
% 3.88/1.01  monotx_time:                            0.
% 3.88/1.01  subtype_inf_time:                       0.013
% 3.88/1.01  
% 3.88/1.01  ------ Problem properties
% 3.88/1.01  
% 3.88/1.01  clauses:                                47
% 3.88/1.01  conjectures:                            23
% 3.88/1.01  epr:                                    13
% 3.88/1.01  horn:                                   31
% 3.88/1.01  ground:                                 23
% 3.88/1.01  unary:                                  14
% 3.88/1.01  binary:                                 18
% 3.88/1.01  lits:                                   163
% 3.88/1.01  lits_eq:                                4
% 3.88/1.01  fd_pure:                                0
% 3.88/1.01  fd_pseudo:                              0
% 3.88/1.01  fd_cond:                                0
% 3.88/1.01  fd_pseudo_cond:                         0
% 3.88/1.01  ac_symbols:                             0
% 3.88/1.01  
% 3.88/1.01  ------ Propositional Solver
% 3.88/1.01  
% 3.88/1.01  prop_solver_calls:                      30
% 3.88/1.01  prop_fast_solver_calls:                 2951
% 3.88/1.01  smt_solver_calls:                       0
% 3.88/1.01  smt_fast_solver_calls:                  0
% 3.88/1.01  prop_num_of_clauses:                    4120
% 3.88/1.01  prop_preprocess_simplified:             12116
% 3.88/1.01  prop_fo_subsumed:                       241
% 3.88/1.01  prop_solver_time:                       0.
% 3.88/1.01  smt_solver_time:                        0.
% 3.88/1.01  smt_fast_solver_time:                   0.
% 3.88/1.01  prop_fast_solver_time:                  0.
% 3.88/1.01  prop_unsat_core_time:                   0.
% 3.88/1.01  
% 3.88/1.01  ------ QBF
% 3.88/1.01  
% 3.88/1.01  qbf_q_res:                              0
% 3.88/1.01  qbf_num_tautologies:                    0
% 3.88/1.01  qbf_prep_cycles:                        0
% 3.88/1.01  
% 3.88/1.01  ------ BMC1
% 3.88/1.01  
% 3.88/1.01  bmc1_current_bound:                     -1
% 3.88/1.01  bmc1_last_solved_bound:                 -1
% 3.88/1.01  bmc1_unsat_core_size:                   -1
% 3.88/1.01  bmc1_unsat_core_parents_size:           -1
% 3.88/1.01  bmc1_merge_next_fun:                    0
% 3.88/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.88/1.01  
% 3.88/1.01  ------ Instantiation
% 3.88/1.01  
% 3.88/1.01  inst_num_of_clauses:                    1195
% 3.88/1.01  inst_num_in_passive:                    392
% 3.88/1.01  inst_num_in_active:                     633
% 3.88/1.01  inst_num_in_unprocessed:                170
% 3.88/1.01  inst_num_of_loops:                      680
% 3.88/1.01  inst_num_of_learning_restarts:          0
% 3.88/1.01  inst_num_moves_active_passive:          44
% 3.88/1.01  inst_lit_activity:                      0
% 3.88/1.01  inst_lit_activity_moves:                1
% 3.88/1.01  inst_num_tautologies:                   0
% 3.88/1.01  inst_num_prop_implied:                  0
% 3.88/1.01  inst_num_existing_simplified:           0
% 3.88/1.01  inst_num_eq_res_simplified:             0
% 3.88/1.01  inst_num_child_elim:                    0
% 3.88/1.01  inst_num_of_dismatching_blockings:      1020
% 3.88/1.01  inst_num_of_non_proper_insts:           1131
% 3.88/1.01  inst_num_of_duplicates:                 0
% 3.88/1.01  inst_inst_num_from_inst_to_res:         0
% 3.88/1.01  inst_dismatching_checking_time:         0.
% 3.88/1.01  
% 3.88/1.01  ------ Resolution
% 3.88/1.01  
% 3.88/1.01  res_num_of_clauses:                     0
% 3.88/1.01  res_num_in_passive:                     0
% 3.88/1.01  res_num_in_active:                      0
% 3.88/1.01  res_num_of_loops:                       243
% 3.88/1.01  res_forward_subset_subsumed:            88
% 3.88/1.01  res_backward_subset_subsumed:           0
% 3.88/1.01  res_forward_subsumed:                   0
% 3.88/1.01  res_backward_subsumed:                  0
% 3.88/1.01  res_forward_subsumption_resolution:     0
% 3.88/1.01  res_backward_subsumption_resolution:    0
% 3.88/1.01  res_clause_to_clause_subsumption:       708
% 3.88/1.01  res_orphan_elimination:                 0
% 3.88/1.01  res_tautology_del:                      82
% 3.88/1.01  res_num_eq_res_simplified:              0
% 3.88/1.01  res_num_sel_changes:                    0
% 3.88/1.01  res_moves_from_active_to_pass:          0
% 3.88/1.01  
% 3.88/1.01  ------ Superposition
% 3.88/1.01  
% 3.88/1.01  sup_time_total:                         0.
% 3.88/1.01  sup_time_generating:                    0.
% 3.88/1.01  sup_time_sim_full:                      0.
% 3.88/1.01  sup_time_sim_immed:                     0.
% 3.88/1.01  
% 3.88/1.01  sup_num_of_clauses:                     229
% 3.88/1.01  sup_num_in_active:                      114
% 3.88/1.01  sup_num_in_passive:                     115
% 3.88/1.01  sup_num_of_loops:                       135
% 3.88/1.01  sup_fw_superposition:                   116
% 3.88/1.01  sup_bw_superposition:                   128
% 3.88/1.01  sup_immediate_simplified:               77
% 3.88/1.01  sup_given_eliminated:                   0
% 3.88/1.01  comparisons_done:                       0
% 3.88/1.01  comparisons_avoided:                    0
% 3.88/1.01  
% 3.88/1.01  ------ Simplifications
% 3.88/1.01  
% 3.88/1.01  
% 3.88/1.01  sim_fw_subset_subsumed:                 6
% 3.88/1.01  sim_bw_subset_subsumed:                 8
% 3.88/1.01  sim_fw_subsumed:                        6
% 3.88/1.01  sim_bw_subsumed:                        4
% 3.88/1.01  sim_fw_subsumption_res:                 0
% 3.88/1.01  sim_bw_subsumption_res:                 0
% 3.88/1.01  sim_tautology_del:                      10
% 3.88/1.01  sim_eq_tautology_del:                   10
% 3.88/1.01  sim_eq_res_simp:                        0
% 3.88/1.01  sim_fw_demodulated:                     3
% 3.88/1.01  sim_bw_demodulated:                     18
% 3.88/1.01  sim_light_normalised:                   79
% 3.88/1.01  sim_joinable_taut:                      0
% 3.88/1.01  sim_joinable_simp:                      0
% 3.88/1.01  sim_ac_normalised:                      0
% 3.88/1.01  sim_smt_subsumption:                    0
% 3.88/1.01  
%------------------------------------------------------------------------------
