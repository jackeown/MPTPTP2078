%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:20 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :  224 (6043 expanded)
%              Number of clauses        :  151 (1094 expanded)
%              Number of leaves         :   12 (2232 expanded)
%              Depth                    :   22
%              Number of atoms          : 1571 (208320 expanded)
%              Number of equality atoms :  388 (8125 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal clause size      :   78 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
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

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f34,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f28,f33,f32,f31,f30,f29])).

fof(f66,plain,(
    m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
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

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f36,plain,(
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
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f34])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
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

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f35,plain,(
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
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f63,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f64,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
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

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f18,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( sP0(X1,X3,X4,X2,X0)
    <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP0(X1,X3,X4,X2,X0)
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
        | ~ sP0(X1,X3,X4,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f25,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP0(X1,X3,X4,X2,X0)
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
        | ~ sP0(X1,X3,X4,X2,X0) ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
        | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
        | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
        | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) )
      & ( ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
          & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
          & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
          & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f25])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f19,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
      <=> sP0(X1,X3,X4,X2,X0) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f21,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(X4) )
          | ~ sP0(X1,X3,X4,X2,X0) )
        & ( sP0(X1,X3,X4,X2,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(X4) ) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f22,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(X4) )
          | ~ sP0(X1,X3,X4,X2,X0) )
        & ( sP0(X1,X3,X4,X2,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(X4) ) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    inference(flattening,[],[f21])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
            & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
            & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
            & v1_funct_1(X2) )
          | ~ sP0(X4,X3,X2,X1,X0) )
        & ( sP0(X4,X3,X2,X1,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
          | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
          | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f22])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
      | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(X2)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
    r4_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f101,plain,
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
    inference(cnf_transformation,[],[f34])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                        <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(flattening,[],[f14])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X0,X2,X4,X3,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(definition_folding,[],[f15,f19,f18])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X2,X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f99,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f95,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f91,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f83,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_54,negated_conjecture,
    ( m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_725,negated_conjecture,
    ( m1_pre_topc(sK6,sK2) ),
    inference(subtyping,[status(esa)],[c_54])).

cnf(c_1539,plain,
    ( m1_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_725])).

cnf(c_58,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_721,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_58])).

cnf(c_1543,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_721])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_753,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ m1_pre_topc(X2_52,X0_52)
    | ~ m1_pre_topc(X2_52,X3_52)
    | ~ m1_pre_topc(X0_52,X3_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X3_52)
    | ~ v2_pre_topc(X3_52)
    | ~ v2_pre_topc(X1_52)
    | ~ l1_pre_topc(X3_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_51,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_51) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1512,plain,
    ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_51,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_51)
    | v1_funct_2(X0_51,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_pre_topc(X2_52,X3_52) != iProver_top
    | m1_pre_topc(X0_52,X3_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X3_52) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X3_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X3_52) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_753])).

cnf(c_2425,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK3,sK2,X0_52,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(X0_52,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1543,c_1512])).

cnf(c_63,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_70,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63])).

cnf(c_62,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_71,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_61,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_72,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_60,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_73,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_59,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_74,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_2932,plain,
    ( v2_pre_topc(X1_52) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK3,sK2,X0_52,sK4)
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(X0_52,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2425,c_70,c_71,c_72,c_73,c_74])).

cnf(c_2933,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK3,sK2,X0_52,sK4)
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(X0_52,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_2932])).

cnf(c_2945,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK6)) = k3_tmap_1(sK2,sK3,sK2,sK6,sK4)
    | m1_pre_topc(sK6,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1539,c_2933])).

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
    inference(cnf_transformation,[],[f35])).

cnf(c_754,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ m1_pre_topc(X2_52,X0_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(X1_52)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_51,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_51,X2_52) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1511,plain,
    ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_51,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_51,X2_52)
    | v1_funct_2(X0_51,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_2186,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK2,sK3,sK4,X0_52)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_52,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1543,c_1511])).

cnf(c_66,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_67,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66])).

cnf(c_65,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_68,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65])).

cnf(c_64,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_69,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64])).

cnf(c_2855,plain,
    ( m1_pre_topc(X0_52,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK2,sK3,sK4,X0_52) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2186,c_67,c_68,c_69,c_70,c_71,c_72,c_73,c_74])).

cnf(c_2856,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK2,sK3,sK4,X0_52)
    | m1_pre_topc(X0_52,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2855])).

cnf(c_2863,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK6)) = k2_tmap_1(sK2,sK3,sK4,sK6) ),
    inference(superposition,[status(thm)],[c_1539,c_2856])).

cnf(c_2966,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK6,sK4) = k2_tmap_1(sK2,sK3,sK4,sK6)
    | m1_pre_topc(sK6,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2945,c_2863])).

cnf(c_57,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_76,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_56,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_77,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_55,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_78,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_79,plain,
    ( m1_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_53,negated_conjecture,
    ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_726,negated_conjecture,
    ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(subtyping,[status(esa)],[c_53])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_752,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_pre_topc(X2_52,X1_52)
    | m1_pre_topc(k1_tsep_1(X1_52,X2_52,X0_52),X1_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X1_52) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1513,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(X2_52,X1_52) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1_52,X2_52,X0_52),X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_752])).

cnf(c_3396,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_726,c_1513])).

cnf(c_5017,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK6,sK4) = k2_tmap_1(sK2,sK3,sK4,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2966,c_67,c_68,c_69,c_76,c_77,c_78,c_79,c_3396])).

cnf(c_9,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_745,plain,
    ( sP0(X0_52,X1_52,X0_51,X2_52,X3_52)
    | ~ v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),X1_52,X0_52)
    | ~ v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),X2_52,X0_52)
    | ~ v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),u1_struct_0(X1_52),u1_struct_0(X0_52))
    | ~ v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),u1_struct_0(X2_52),u1_struct_0(X0_52))
    | ~ m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52))))
    | ~ m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X0_52))))
    | ~ v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51))
    | ~ v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1520,plain,
    ( sP0(X0_52,X1_52,X0_51,X2_52,X3_52) = iProver_top
    | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),X1_52,X0_52) != iProver_top
    | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),X2_52,X0_52) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),u1_struct_0(X2_52),u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X0_52)))) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51)) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_745])).

cnf(c_9166,plain,
    ( sP0(X0_52,sK6,X0_51,sK5,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK5,X0_51),sK5,X0_52) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK6,X0_51),sK6,X0_52) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK5,X0_51),u1_struct_0(sK5),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK6,X0_51),u1_struct_0(sK6),u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK5,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_52)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK5,X0_51)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK6,X0_51)) != iProver_top ),
    inference(superposition,[status(thm)],[c_726,c_1520])).

cnf(c_9176,plain,
    ( sP0(X0_52,sK6,X0_51,sK5,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_51),sK5,X0_52) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_51),sK6,X0_52) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_51),u1_struct_0(sK5),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_51),u1_struct_0(sK6),u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_52)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_51)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_51)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9166,c_726])).

cnf(c_9367,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,sK4),sK5,sK3) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK6,sK4),sK6,sK3) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,sK4),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK6,sK4),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,sK4)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK6,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5017,c_9176])).

cnf(c_723,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(subtyping,[status(esa)],[c_56])).

cnf(c_1541,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_723])).

cnf(c_2946,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK5)) = k3_tmap_1(sK2,sK3,sK2,sK5,sK4)
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1541,c_2933])).

cnf(c_2864,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK5)) = k2_tmap_1(sK2,sK3,sK4,sK5) ),
    inference(superposition,[status(thm)],[c_1541,c_2856])).

cnf(c_2953,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,sK4) = k2_tmap_1(sK2,sK3,sK4,sK5)
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2946,c_2864])).

cnf(c_4920,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,sK4) = k2_tmap_1(sK2,sK3,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2953,c_67,c_68,c_69,c_76,c_77,c_78,c_79,c_3396])).

cnf(c_9377,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9367,c_4920,c_5017])).

cnf(c_8,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | sP0(X4,X3,X2,X1,X0)
    | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_746,plain,
    ( ~ sP1(X0_52,X1_52,X0_51,X2_52,X3_52)
    | sP0(X3_52,X2_52,X0_51,X1_52,X0_52)
    | ~ v5_pre_topc(X0_51,k1_tsep_1(X0_52,X1_52,X2_52),X3_52)
    | ~ v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))))
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1519,plain,
    ( sP1(X0_52,X1_52,X0_51,X2_52,X3_52) != iProver_top
    | sP0(X3_52,X2_52,X0_51,X1_52,X0_52) = iProver_top
    | v5_pre_topc(X0_51,k1_tsep_1(X0_52,X1_52,X2_52),X3_52) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_746])).

cnf(c_8204,plain,
    ( sP1(sK2,sK5,X0_51,sK6,X0_52) != iProver_top
    | sP0(X0_52,sK6,X0_51,sK5,sK2) = iProver_top
    | v5_pre_topc(X0_51,k1_tsep_1(sK2,sK5,sK6),X0_52) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_726,c_1519])).

cnf(c_8211,plain,
    ( sP1(sK2,sK5,X0_51,sK6,X0_52) != iProver_top
    | sP0(X0_52,sK6,X0_51,sK5,sK2) = iProver_top
    | v5_pre_topc(X0_51,sK2,X0_52) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8204,c_726])).

cnf(c_8258,plain,
    ( sP1(sK2,sK5,sK4,sK6,sK3) != iProver_top
    | sP0(sK3,sK6,sK4,sK5,sK2) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1543,c_8211])).

cnf(c_75,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_52,negated_conjecture,
    ( r4_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_80,plain,
    ( r4_tsep_1(sK2,sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_740,plain,
    ( ~ sP0(X0_52,X1_52,X0_51,X2_52,X3_52)
    | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X0_52)))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1525,plain,
    ( sP0(X0_52,X1_52,X0_51,X2_52,X3_52) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X0_52)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_740])).

cnf(c_6998,plain,
    ( sP0(X0_52,sK6,X0_51,sK5,sK2) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_52)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_726,c_1525])).

cnf(c_7157,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4920,c_6998])).

cnf(c_19,negated_conjecture,
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
    inference(cnf_transformation,[],[f101])).

cnf(c_482,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_60,c_59,c_58])).

cnf(c_483,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(renaming,[status(thm)],[c_482])).

cnf(c_712,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(subtyping,[status(esa)],[c_483])).

cnf(c_1552,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_712])).

cnf(c_7388,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7157,c_1552])).

cnf(c_484,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_739,plain,
    ( ~ sP0(X0_52,X1_52,X0_51,X2_52,X3_52)
    | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),X2_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1526,plain,
    ( sP0(X0_52,X1_52,X0_51,X2_52,X3_52) != iProver_top
    | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),X2_52,X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_739])).

cnf(c_4728,plain,
    ( sP0(X0_52,sK6,X0_51,sK5,sK2) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_51),sK5,X0_52) = iProver_top ),
    inference(superposition,[status(thm)],[c_726,c_1526])).

cnf(c_4923,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4920,c_4728])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_737,plain,
    ( ~ sP0(X0_52,X1_52,X0_51,X2_52,X3_52)
    | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1528,plain,
    ( sP0(X0_52,X1_52,X0_51,X2_52,X3_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_3681,plain,
    ( sP0(X0_52,sK6,X0_51,sK5,sK2) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_51)) = iProver_top ),
    inference(superposition,[status(thm)],[c_726,c_1528])).

cnf(c_4924,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4920,c_3681])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_743,plain,
    ( ~ sP0(X0_52,X1_52,X0_51,X2_52,X3_52)
    | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),X1_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1522,plain,
    ( sP0(X0_52,X1_52,X0_51,X2_52,X3_52) != iProver_top
    | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),X1_52,X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_4612,plain,
    ( sP0(X0_52,sK6,X0_51,sK5,sK2) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_51),sK6,X0_52) = iProver_top ),
    inference(superposition,[status(thm)],[c_726,c_1522])).

cnf(c_5020,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5017,c_4612])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_741,plain,
    ( ~ sP0(X0_52,X1_52,X0_51,X2_52,X3_52)
    | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1524,plain,
    ( sP0(X0_52,X1_52,X0_51,X2_52,X3_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_3527,plain,
    ( sP0(X0_52,sK6,X0_51,sK5,sK2) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_51)) = iProver_top ),
    inference(superposition,[status(thm)],[c_726,c_1524])).

cnf(c_5021,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5017,c_3527])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_742,plain,
    ( ~ sP0(X0_52,X1_52,X0_51,X2_52,X3_52)
    | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),u1_struct_0(X1_52),u1_struct_0(X0_52)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1523,plain,
    ( sP0(X0_52,X1_52,X0_51,X2_52,X3_52) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),u1_struct_0(X1_52),u1_struct_0(X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_742])).

cnf(c_5320,plain,
    ( sP0(X0_52,sK6,X0_51,sK5,sK2) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_51),u1_struct_0(sK6),u1_struct_0(X0_52)) = iProver_top ),
    inference(superposition,[status(thm)],[c_726,c_1523])).

cnf(c_5575,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5017,c_5320])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_738,plain,
    ( ~ sP0(X0_52,X1_52,X0_51,X2_52,X3_52)
    | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),u1_struct_0(X2_52),u1_struct_0(X0_52)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1527,plain,
    ( sP0(X0_52,X1_52,X0_51,X2_52,X3_52) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),u1_struct_0(X2_52),u1_struct_0(X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_738])).

cnf(c_5580,plain,
    ( sP0(X0_52,sK6,X0_51,sK5,sK2) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_51),u1_struct_0(sK5),u1_struct_0(X0_52)) = iProver_top ),
    inference(superposition,[status(thm)],[c_726,c_1527])).

cnf(c_5688,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4920,c_5580])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_744,plain,
    ( ~ sP0(X0_52,X1_52,X0_51,X2_52,X3_52)
    | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1521,plain,
    ( sP0(X0_52,X1_52,X0_51,X2_52,X3_52) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_6768,plain,
    ( sP0(X0_52,sK6,X0_51,sK5,sK2) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_52)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_726,c_1521])).

cnf(c_6933,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5017,c_6768])).

cnf(c_7465,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7388,c_484,c_4923,c_4924,c_5020,c_5021,c_5575,c_5688,c_6933,c_7157])).

cnf(c_7466,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_7465])).

cnf(c_18,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ r4_tsep_1(X0,X1,X3)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_736,plain,
    ( sP1(X0_52,X1_52,X0_51,X2_52,X3_52)
    | ~ r4_tsep_1(X0_52,X1_52,X2_52)
    | ~ v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))))
    | ~ m1_pre_topc(X1_52,X0_52)
    | ~ m1_pre_topc(X2_52,X0_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X3_52)
    | v2_struct_0(X2_52)
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(X3_52)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(X3_52)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1529,plain,
    ( sP1(X0_52,X1_52,X0_51,X2_52,X3_52) = iProver_top
    | r4_tsep_1(X0_52,X1_52,X2_52) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52)))) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X3_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X3_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X3_52) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_8342,plain,
    ( sP1(sK2,sK5,X0_51,sK6,X0_52) = iProver_top
    | r4_tsep_1(sK2,sK5,sK6) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_726,c_1529])).

cnf(c_8358,plain,
    ( sP1(sK2,sK5,X0_51,sK6,X0_52) = iProver_top
    | r4_tsep_1(sK2,sK5,sK6) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8342,c_726])).

cnf(c_8441,plain,
    ( sP1(sK2,sK5,sK4,sK6,sK3) = iProver_top
    | r4_tsep_1(sK2,sK5,sK6) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8358])).

cnf(c_8626,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8258,c_67,c_68,c_69,c_70,c_71,c_72,c_73,c_74,c_75,c_76,c_77,c_78,c_79,c_80,c_7466,c_8441])).

cnf(c_5,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_749,plain,
    ( ~ sP1(X0_52,X1_52,X0_51,X2_52,X3_52)
    | ~ sP0(X3_52,X2_52,X0_51,X1_52,X0_52)
    | v5_pre_topc(X0_51,k1_tsep_1(X0_52,X1_52,X2_52),X3_52) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1516,plain,
    ( sP1(X0_52,X1_52,X0_51,X2_52,X3_52) != iProver_top
    | sP0(X3_52,X2_52,X0_51,X1_52,X0_52) != iProver_top
    | v5_pre_topc(X0_51,k1_tsep_1(X0_52,X1_52,X2_52),X3_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_749])).

cnf(c_6584,plain,
    ( sP1(sK2,sK5,X0_51,sK6,X0_52) != iProver_top
    | sP0(X0_52,sK6,X0_51,sK5,sK2) != iProver_top
    | v5_pre_topc(X0_51,sK2,X0_52) = iProver_top ),
    inference(superposition,[status(thm)],[c_726,c_1516])).

cnf(c_6586,plain,
    ( sP1(sK2,sK5,sK4,sK6,sK3) != iProver_top
    | sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6584])).

cnf(c_21,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_111,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_25,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_107,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_29,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_103,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_33,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_99,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_37,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_95,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_41,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_91,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_45,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_87,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_49,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_83,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9377,c_8626,c_8441,c_6586,c_111,c_107,c_103,c_99,c_95,c_91,c_87,c_83,c_80,c_79,c_78,c_77,c_76,c_75,c_74,c_73,c_72,c_71,c_70,c_69,c_68,c_67])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.35  % Computer   : n024.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % WCLimit    : 600
% 0.12/0.35  % DateTime   : Tue Dec  1 18:50:21 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 3.93/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.01  
% 3.93/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.93/1.01  
% 3.93/1.01  ------  iProver source info
% 3.93/1.01  
% 3.93/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.93/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.93/1.01  git: non_committed_changes: false
% 3.93/1.01  git: last_make_outside_of_git: false
% 3.93/1.01  
% 3.93/1.01  ------ 
% 3.93/1.01  ------ Parsing...
% 3.93/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.93/1.01  
% 3.93/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.93/1.01  
% 3.93/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.93/1.01  
% 3.93/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.93/1.01  ------ Proving...
% 3.93/1.01  ------ Problem Properties 
% 3.93/1.01  
% 3.93/1.01  
% 3.93/1.01  clauses                                 43
% 3.93/1.01  conjectures                             24
% 3.93/1.01  EPR                                     13
% 3.93/1.01  Horn                                    30
% 3.93/1.01  unary                                   15
% 3.93/1.01  binary                                  16
% 3.93/1.01  lits                                    136
% 3.93/1.01  lits eq                                 3
% 3.93/1.01  fd_pure                                 0
% 3.93/1.01  fd_pseudo                               0
% 3.93/1.01  fd_cond                                 0
% 3.93/1.01  fd_pseudo_cond                          0
% 3.93/1.01  AC symbols                              0
% 3.93/1.01  
% 3.93/1.01  ------ Input Options Time Limit: Unbounded
% 3.93/1.01  
% 3.93/1.01  
% 3.93/1.01  ------ 
% 3.93/1.01  Current options:
% 3.93/1.01  ------ 
% 3.93/1.01  
% 3.93/1.01  
% 3.93/1.01  
% 3.93/1.01  
% 3.93/1.01  ------ Proving...
% 3.93/1.01  
% 3.93/1.01  
% 3.93/1.01  % SZS status Theorem for theBenchmark.p
% 3.93/1.01  
% 3.93/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.93/1.01  
% 3.93/1.01  fof(f5,conjecture,(
% 3.93/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 3.93/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f6,negated_conjecture,(
% 3.93/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 3.93/1.01    inference(negated_conjecture,[],[f5])).
% 3.93/1.01  
% 3.93/1.01  fof(f16,plain,(
% 3.93/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & (r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0)) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.93/1.01    inference(ennf_transformation,[],[f6])).
% 3.93/1.01  
% 3.93/1.01  fof(f17,plain,(
% 3.93/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.93/1.01    inference(flattening,[],[f16])).
% 3.93/1.01  
% 3.93/1.01  fof(f27,plain,(
% 3.93/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.93/1.01    inference(nnf_transformation,[],[f17])).
% 3.93/1.01  
% 3.93/1.01  fof(f28,plain,(
% 3.93/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.93/1.01    inference(flattening,[],[f27])).
% 3.93/1.01  
% 3.93/1.01  fof(f33,plain,(
% 3.93/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((~m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,sK6) & k1_tsep_1(X0,X3,sK6) = X0 & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 3.93/1.01    introduced(choice_axiom,[])).
% 3.93/1.01  
% 3.93/1.01  fof(f32,plain,(
% 3.93/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK5)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK5))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,sK5,X4) & k1_tsep_1(X0,sK5,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 3.93/1.01    introduced(choice_axiom,[])).
% 3.93/1.01  
% 3.93/1.01  fof(f31,plain,(
% 3.93/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(sK4,X0,X1) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) & m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X3))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK4,X0,X1) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.93/1.01    introduced(choice_axiom,[])).
% 3.93/1.01  
% 3.93/1.01  fof(f30,plain,(
% 3.93/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(X2,X0,sK3) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) & m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v5_pre_topc(X2,X0,sK3) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 3.93/1.01    introduced(choice_axiom,[])).
% 3.93/1.01  
% 3.93/1.01  fof(f29,plain,(
% 3.93/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(sK2,X3,X4) & k1_tsep_1(sK2,X3,X4) = sK2 & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.93/1.01    introduced(choice_axiom,[])).
% 3.93/1.01  
% 3.93/1.01  fof(f34,plain,(
% 3.93/1.01    (((((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,sK5,sK6) & k1_tsep_1(sK2,sK5,sK6) = sK2 & m1_pre_topc(sK6,sK2) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.93/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f28,f33,f32,f31,f30,f29])).
% 3.93/1.01  
% 3.93/1.01  fof(f66,plain,(
% 3.93/1.01    m1_pre_topc(sK6,sK2)),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f62,plain,(
% 3.93/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f2,axiom,(
% 3.93/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.93/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f10,plain,(
% 3.93/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.93/1.01    inference(ennf_transformation,[],[f2])).
% 3.93/1.01  
% 3.93/1.01  fof(f11,plain,(
% 3.93/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.93/1.01    inference(flattening,[],[f10])).
% 3.93/1.01  
% 3.93/1.01  fof(f36,plain,(
% 3.93/1.01    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f11])).
% 3.93/1.01  
% 3.93/1.01  fof(f57,plain,(
% 3.93/1.01    ~v2_struct_0(sK3)),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f58,plain,(
% 3.93/1.01    v2_pre_topc(sK3)),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f59,plain,(
% 3.93/1.01    l1_pre_topc(sK3)),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f60,plain,(
% 3.93/1.01    v1_funct_1(sK4)),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f61,plain,(
% 3.93/1.01    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f1,axiom,(
% 3.93/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.93/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f8,plain,(
% 3.93/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.93/1.01    inference(ennf_transformation,[],[f1])).
% 3.93/1.01  
% 3.93/1.01  fof(f9,plain,(
% 3.93/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.93/1.01    inference(flattening,[],[f8])).
% 3.93/1.01  
% 3.93/1.01  fof(f35,plain,(
% 3.93/1.01    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f9])).
% 3.93/1.01  
% 3.93/1.01  fof(f54,plain,(
% 3.93/1.01    ~v2_struct_0(sK2)),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f55,plain,(
% 3.93/1.01    v2_pre_topc(sK2)),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f56,plain,(
% 3.93/1.01    l1_pre_topc(sK2)),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f63,plain,(
% 3.93/1.01    ~v2_struct_0(sK5)),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f64,plain,(
% 3.93/1.01    m1_pre_topc(sK5,sK2)),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f65,plain,(
% 3.93/1.01    ~v2_struct_0(sK6)),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f67,plain,(
% 3.93/1.01    k1_tsep_1(sK2,sK5,sK6) = sK2),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f3,axiom,(
% 3.93/1.01    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.93/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f7,plain,(
% 3.93/1.01    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.93/1.01    inference(pure_predicate_removal,[],[f3])).
% 3.93/1.01  
% 3.93/1.01  fof(f12,plain,(
% 3.93/1.01    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.93/1.01    inference(ennf_transformation,[],[f7])).
% 3.93/1.01  
% 3.93/1.01  fof(f13,plain,(
% 3.93/1.01    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.93/1.01    inference(flattening,[],[f12])).
% 3.93/1.01  
% 3.93/1.01  fof(f38,plain,(
% 3.93/1.01    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f13])).
% 3.93/1.01  
% 3.93/1.01  fof(f18,plain,(
% 3.93/1.01    ! [X1,X3,X4,X2,X0] : (sP0(X1,X3,X4,X2,X0) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))),
% 3.93/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.93/1.01  
% 3.93/1.01  fof(f24,plain,(
% 3.93/1.01    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 3.93/1.01    inference(nnf_transformation,[],[f18])).
% 3.93/1.01  
% 3.93/1.01  fof(f25,plain,(
% 3.93/1.01    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 3.93/1.01    inference(flattening,[],[f24])).
% 3.93/1.01  
% 3.93/1.01  fof(f26,plain,(
% 3.93/1.01    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) & ((m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) | ~sP0(X0,X1,X2,X3,X4)))),
% 3.93/1.01    inference(rectify,[],[f25])).
% 3.93/1.01  
% 3.93/1.01  fof(f52,plain,(
% 3.93/1.01    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) )),
% 3.93/1.01    inference(cnf_transformation,[],[f26])).
% 3.93/1.01  
% 3.93/1.01  fof(f19,plain,(
% 3.93/1.01    ! [X0,X2,X4,X3,X1] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> sP0(X1,X3,X4,X2,X0)) | ~sP1(X0,X2,X4,X3,X1))),
% 3.93/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.93/1.01  
% 3.93/1.01  fof(f21,plain,(
% 3.93/1.01    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)))) | ~sP1(X0,X2,X4,X3,X1))),
% 3.93/1.01    inference(nnf_transformation,[],[f19])).
% 3.93/1.01  
% 3.93/1.01  fof(f22,plain,(
% 3.93/1.01    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~sP1(X0,X2,X4,X3,X1))),
% 3.93/1.01    inference(flattening,[],[f21])).
% 3.93/1.01  
% 3.93/1.01  fof(f23,plain,(
% 3.93/1.01    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) & v1_funct_1(X2)) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) | ~v1_funct_1(X2))) | ~sP1(X0,X1,X2,X3,X4))),
% 3.93/1.01    inference(rectify,[],[f22])).
% 3.93/1.01  
% 3.93/1.01  fof(f39,plain,(
% 3.93/1.01    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) | ~v1_funct_1(X2) | ~sP1(X0,X1,X2,X3,X4)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f23])).
% 3.93/1.01  
% 3.93/1.01  fof(f68,plain,(
% 3.93/1.01    r4_tsep_1(sK2,sK5,sK6)),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f47,plain,(
% 3.93/1.01    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f26])).
% 3.93/1.01  
% 3.93/1.01  fof(f101,plain,(
% 3.93/1.01    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f46,plain,(
% 3.93/1.01    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f26])).
% 3.93/1.01  
% 3.93/1.01  fof(f44,plain,(
% 3.93/1.01    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f26])).
% 3.93/1.01  
% 3.93/1.01  fof(f50,plain,(
% 3.93/1.01    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f26])).
% 3.93/1.01  
% 3.93/1.01  fof(f48,plain,(
% 3.93/1.01    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f26])).
% 3.93/1.01  
% 3.93/1.01  fof(f49,plain,(
% 3.93/1.01    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f26])).
% 3.93/1.01  
% 3.93/1.01  fof(f45,plain,(
% 3.93/1.01    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f26])).
% 3.93/1.01  
% 3.93/1.01  fof(f51,plain,(
% 3.93/1.01    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f26])).
% 3.93/1.01  
% 3.93/1.01  fof(f4,axiom,(
% 3.93/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))))))))),
% 3.93/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f14,plain,(
% 3.93/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.93/1.01    inference(ennf_transformation,[],[f4])).
% 3.93/1.01  
% 3.93/1.01  fof(f15,plain,(
% 3.93/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.93/1.01    inference(flattening,[],[f14])).
% 3.93/1.01  
% 3.93/1.01  fof(f20,plain,(
% 3.93/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.93/1.01    inference(definition_folding,[],[f15,f19,f18])).
% 3.93/1.01  
% 3.93/1.01  fof(f53,plain,(
% 3.93/1.01    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f20])).
% 3.93/1.01  
% 3.93/1.01  fof(f42,plain,(
% 3.93/1.01    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f23])).
% 3.93/1.01  
% 3.93/1.01  fof(f99,plain,(
% 3.93/1.01    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f95,plain,(
% 3.93/1.01    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f91,plain,(
% 3.93/1.01    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f87,plain,(
% 3.93/1.01    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | v5_pre_topc(sK4,sK2,sK3)),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f83,plain,(
% 3.93/1.01    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f79,plain,(
% 3.93/1.01    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 3.93/1.01    inference(cnf_transformation,[],[f34])).
% 3.93/1.02  
% 3.93/1.02  fof(f75,plain,(
% 3.93/1.02    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 3.93/1.02    inference(cnf_transformation,[],[f34])).
% 3.93/1.02  
% 3.93/1.02  fof(f71,plain,(
% 3.93/1.02    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | v5_pre_topc(sK4,sK2,sK3)),
% 3.93/1.02    inference(cnf_transformation,[],[f34])).
% 3.93/1.02  
% 3.93/1.02  cnf(c_54,negated_conjecture,
% 3.93/1.02      ( m1_pre_topc(sK6,sK2) ),
% 3.93/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_725,negated_conjecture,
% 3.93/1.02      ( m1_pre_topc(sK6,sK2) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_54]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1539,plain,
% 3.93/1.02      ( m1_pre_topc(sK6,sK2) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_725]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_58,negated_conjecture,
% 3.93/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 3.93/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_721,negated_conjecture,
% 3.93/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_58]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1543,plain,
% 3.93/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_721]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1,plain,
% 3.93/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.93/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.93/1.02      | ~ m1_pre_topc(X3,X4)
% 3.93/1.02      | ~ m1_pre_topc(X3,X1)
% 3.93/1.02      | ~ m1_pre_topc(X1,X4)
% 3.93/1.02      | v2_struct_0(X4)
% 3.93/1.02      | v2_struct_0(X2)
% 3.93/1.02      | ~ v2_pre_topc(X2)
% 3.93/1.02      | ~ v2_pre_topc(X4)
% 3.93/1.02      | ~ l1_pre_topc(X2)
% 3.93/1.02      | ~ l1_pre_topc(X4)
% 3.93/1.02      | ~ v1_funct_1(X0)
% 3.93/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 3.93/1.02      inference(cnf_transformation,[],[f36]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_753,plain,
% 3.93/1.02      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 3.93/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 3.93/1.02      | ~ m1_pre_topc(X2_52,X0_52)
% 3.93/1.02      | ~ m1_pre_topc(X2_52,X3_52)
% 3.93/1.02      | ~ m1_pre_topc(X0_52,X3_52)
% 3.93/1.02      | v2_struct_0(X1_52)
% 3.93/1.02      | v2_struct_0(X3_52)
% 3.93/1.02      | ~ v2_pre_topc(X3_52)
% 3.93/1.02      | ~ v2_pre_topc(X1_52)
% 3.93/1.02      | ~ l1_pre_topc(X3_52)
% 3.93/1.02      | ~ l1_pre_topc(X1_52)
% 3.93/1.02      | ~ v1_funct_1(X0_51)
% 3.93/1.02      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_51,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_51) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1512,plain,
% 3.93/1.02      ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_51,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_51)
% 3.93/1.02      | v1_funct_2(X0_51,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 3.93/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 3.93/1.02      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 3.93/1.02      | m1_pre_topc(X2_52,X3_52) != iProver_top
% 3.93/1.02      | m1_pre_topc(X0_52,X3_52) != iProver_top
% 3.93/1.02      | v2_struct_0(X1_52) = iProver_top
% 3.93/1.02      | v2_struct_0(X3_52) = iProver_top
% 3.93/1.02      | v2_pre_topc(X1_52) != iProver_top
% 3.93/1.02      | v2_pre_topc(X3_52) != iProver_top
% 3.93/1.02      | l1_pre_topc(X1_52) != iProver_top
% 3.93/1.02      | l1_pre_topc(X3_52) != iProver_top
% 3.93/1.02      | v1_funct_1(X0_51) != iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_753]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2425,plain,
% 3.93/1.02      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK3,sK2,X0_52,sK4)
% 3.93/1.02      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.93/1.02      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 3.93/1.02      | m1_pre_topc(X0_52,sK2) != iProver_top
% 3.93/1.02      | m1_pre_topc(sK2,X1_52) != iProver_top
% 3.93/1.02      | v2_struct_0(X1_52) = iProver_top
% 3.93/1.02      | v2_struct_0(sK3) = iProver_top
% 3.93/1.02      | v2_pre_topc(X1_52) != iProver_top
% 3.93/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.93/1.02      | l1_pre_topc(X1_52) != iProver_top
% 3.93/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.93/1.02      | v1_funct_1(sK4) != iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_1543,c_1512]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_63,negated_conjecture,
% 3.93/1.02      ( ~ v2_struct_0(sK3) ),
% 3.93/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_70,plain,
% 3.93/1.02      ( v2_struct_0(sK3) != iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_63]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_62,negated_conjecture,
% 3.93/1.02      ( v2_pre_topc(sK3) ),
% 3.93/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_71,plain,
% 3.93/1.02      ( v2_pre_topc(sK3) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_61,negated_conjecture,
% 3.93/1.02      ( l1_pre_topc(sK3) ),
% 3.93/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_72,plain,
% 3.93/1.02      ( l1_pre_topc(sK3) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_60,negated_conjecture,
% 3.93/1.02      ( v1_funct_1(sK4) ),
% 3.93/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_73,plain,
% 3.93/1.02      ( v1_funct_1(sK4) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_59,negated_conjecture,
% 3.93/1.02      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 3.93/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_74,plain,
% 3.93/1.02      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2932,plain,
% 3.93/1.02      ( v2_pre_topc(X1_52) != iProver_top
% 3.93/1.02      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK3,sK2,X0_52,sK4)
% 3.93/1.02      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 3.93/1.02      | m1_pre_topc(X0_52,sK2) != iProver_top
% 3.93/1.02      | m1_pre_topc(sK2,X1_52) != iProver_top
% 3.93/1.02      | v2_struct_0(X1_52) = iProver_top
% 3.93/1.02      | l1_pre_topc(X1_52) != iProver_top ),
% 3.93/1.02      inference(global_propositional_subsumption,
% 3.93/1.02                [status(thm)],
% 3.93/1.02                [c_2425,c_70,c_71,c_72,c_73,c_74]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2933,plain,
% 3.93/1.02      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK3,sK2,X0_52,sK4)
% 3.93/1.02      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 3.93/1.02      | m1_pre_topc(X0_52,sK2) != iProver_top
% 3.93/1.02      | m1_pre_topc(sK2,X1_52) != iProver_top
% 3.93/1.02      | v2_struct_0(X1_52) = iProver_top
% 3.93/1.02      | v2_pre_topc(X1_52) != iProver_top
% 3.93/1.02      | l1_pre_topc(X1_52) != iProver_top ),
% 3.93/1.02      inference(renaming,[status(thm)],[c_2932]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2945,plain,
% 3.93/1.02      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK6)) = k3_tmap_1(sK2,sK3,sK2,sK6,sK4)
% 3.93/1.02      | m1_pre_topc(sK6,sK2) != iProver_top
% 3.93/1.02      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.93/1.02      | v2_struct_0(sK2) = iProver_top
% 3.93/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.93/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_1539,c_2933]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_0,plain,
% 3.93/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.93/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.93/1.02      | ~ m1_pre_topc(X3,X1)
% 3.93/1.02      | v2_struct_0(X1)
% 3.93/1.02      | v2_struct_0(X2)
% 3.93/1.02      | ~ v2_pre_topc(X2)
% 3.93/1.02      | ~ v2_pre_topc(X1)
% 3.93/1.02      | ~ l1_pre_topc(X2)
% 3.93/1.02      | ~ l1_pre_topc(X1)
% 3.93/1.02      | ~ v1_funct_1(X0)
% 3.93/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.93/1.02      inference(cnf_transformation,[],[f35]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_754,plain,
% 3.93/1.02      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 3.93/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 3.93/1.02      | ~ m1_pre_topc(X2_52,X0_52)
% 3.93/1.02      | v2_struct_0(X0_52)
% 3.93/1.02      | v2_struct_0(X1_52)
% 3.93/1.02      | ~ v2_pre_topc(X0_52)
% 3.93/1.02      | ~ v2_pre_topc(X1_52)
% 3.93/1.02      | ~ l1_pre_topc(X0_52)
% 3.93/1.02      | ~ l1_pre_topc(X1_52)
% 3.93/1.02      | ~ v1_funct_1(X0_51)
% 3.93/1.02      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_51,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_51,X2_52) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_0]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1511,plain,
% 3.93/1.02      ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_51,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_51,X2_52)
% 3.93/1.02      | v1_funct_2(X0_51,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 3.93/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 3.93/1.02      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 3.93/1.02      | v2_struct_0(X0_52) = iProver_top
% 3.93/1.02      | v2_struct_0(X1_52) = iProver_top
% 3.93/1.02      | v2_pre_topc(X0_52) != iProver_top
% 3.93/1.02      | v2_pre_topc(X1_52) != iProver_top
% 3.93/1.02      | l1_pre_topc(X0_52) != iProver_top
% 3.93/1.02      | l1_pre_topc(X1_52) != iProver_top
% 3.93/1.02      | v1_funct_1(X0_51) != iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2186,plain,
% 3.93/1.02      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK2,sK3,sK4,X0_52)
% 3.93/1.02      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.93/1.02      | m1_pre_topc(X0_52,sK2) != iProver_top
% 3.93/1.02      | v2_struct_0(sK3) = iProver_top
% 3.93/1.02      | v2_struct_0(sK2) = iProver_top
% 3.93/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.93/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.93/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.93/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.93/1.02      | v1_funct_1(sK4) != iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_1543,c_1511]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_66,negated_conjecture,
% 3.93/1.02      ( ~ v2_struct_0(sK2) ),
% 3.93/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_67,plain,
% 3.93/1.02      ( v2_struct_0(sK2) != iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_66]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_65,negated_conjecture,
% 3.93/1.02      ( v2_pre_topc(sK2) ),
% 3.93/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_68,plain,
% 3.93/1.02      ( v2_pre_topc(sK2) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_65]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_64,negated_conjecture,
% 3.93/1.02      ( l1_pre_topc(sK2) ),
% 3.93/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_69,plain,
% 3.93/1.02      ( l1_pre_topc(sK2) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_64]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2855,plain,
% 3.93/1.02      ( m1_pre_topc(X0_52,sK2) != iProver_top
% 3.93/1.02      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK2,sK3,sK4,X0_52) ),
% 3.93/1.02      inference(global_propositional_subsumption,
% 3.93/1.02                [status(thm)],
% 3.93/1.02                [c_2186,c_67,c_68,c_69,c_70,c_71,c_72,c_73,c_74]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2856,plain,
% 3.93/1.02      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK2,sK3,sK4,X0_52)
% 3.93/1.02      | m1_pre_topc(X0_52,sK2) != iProver_top ),
% 3.93/1.02      inference(renaming,[status(thm)],[c_2855]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2863,plain,
% 3.93/1.02      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK6)) = k2_tmap_1(sK2,sK3,sK4,sK6) ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_1539,c_2856]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2966,plain,
% 3.93/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK6,sK4) = k2_tmap_1(sK2,sK3,sK4,sK6)
% 3.93/1.02      | m1_pre_topc(sK6,sK2) != iProver_top
% 3.93/1.02      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.93/1.02      | v2_struct_0(sK2) = iProver_top
% 3.93/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.93/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 3.93/1.02      inference(light_normalisation,[status(thm)],[c_2945,c_2863]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_57,negated_conjecture,
% 3.93/1.02      ( ~ v2_struct_0(sK5) ),
% 3.93/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_76,plain,
% 3.93/1.02      ( v2_struct_0(sK5) != iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_56,negated_conjecture,
% 3.93/1.02      ( m1_pre_topc(sK5,sK2) ),
% 3.93/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_77,plain,
% 3.93/1.02      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_55,negated_conjecture,
% 3.93/1.02      ( ~ v2_struct_0(sK6) ),
% 3.93/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_78,plain,
% 3.93/1.02      ( v2_struct_0(sK6) != iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_79,plain,
% 3.93/1.02      ( m1_pre_topc(sK6,sK2) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_53,negated_conjecture,
% 3.93/1.02      ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
% 3.93/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_726,negated_conjecture,
% 3.93/1.02      ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_53]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2,plain,
% 3.93/1.02      ( ~ m1_pre_topc(X0,X1)
% 3.93/1.02      | ~ m1_pre_topc(X2,X1)
% 3.93/1.02      | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 3.93/1.02      | v2_struct_0(X1)
% 3.93/1.02      | v2_struct_0(X2)
% 3.93/1.02      | v2_struct_0(X0)
% 3.93/1.02      | ~ l1_pre_topc(X1) ),
% 3.93/1.02      inference(cnf_transformation,[],[f38]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_752,plain,
% 3.93/1.02      ( ~ m1_pre_topc(X0_52,X1_52)
% 3.93/1.02      | ~ m1_pre_topc(X2_52,X1_52)
% 3.93/1.02      | m1_pre_topc(k1_tsep_1(X1_52,X2_52,X0_52),X1_52)
% 3.93/1.02      | v2_struct_0(X0_52)
% 3.93/1.02      | v2_struct_0(X1_52)
% 3.93/1.02      | v2_struct_0(X2_52)
% 3.93/1.02      | ~ l1_pre_topc(X1_52) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1513,plain,
% 3.93/1.02      ( m1_pre_topc(X0_52,X1_52) != iProver_top
% 3.93/1.02      | m1_pre_topc(X2_52,X1_52) != iProver_top
% 3.93/1.02      | m1_pre_topc(k1_tsep_1(X1_52,X2_52,X0_52),X1_52) = iProver_top
% 3.93/1.02      | v2_struct_0(X0_52) = iProver_top
% 3.93/1.02      | v2_struct_0(X1_52) = iProver_top
% 3.93/1.02      | v2_struct_0(X2_52) = iProver_top
% 3.93/1.02      | l1_pre_topc(X1_52) != iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_752]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_3396,plain,
% 3.93/1.02      ( m1_pre_topc(sK5,sK2) != iProver_top
% 3.93/1.02      | m1_pre_topc(sK6,sK2) != iProver_top
% 3.93/1.02      | m1_pre_topc(sK2,sK2) = iProver_top
% 3.93/1.02      | v2_struct_0(sK5) = iProver_top
% 3.93/1.02      | v2_struct_0(sK6) = iProver_top
% 3.93/1.02      | v2_struct_0(sK2) = iProver_top
% 3.93/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_726,c_1513]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_5017,plain,
% 3.93/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK6,sK4) = k2_tmap_1(sK2,sK3,sK4,sK6) ),
% 3.93/1.02      inference(global_propositional_subsumption,
% 3.93/1.02                [status(thm)],
% 3.93/1.02                [c_2966,c_67,c_68,c_69,c_76,c_77,c_78,c_79,c_3396]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_9,plain,
% 3.93/1.02      ( sP0(X0,X1,X2,X3,X4)
% 3.93/1.02      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
% 3.93/1.02      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
% 3.93/1.02      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
% 3.93/1.02      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
% 3.93/1.02      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 3.93/1.02      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
% 3.93/1.02      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
% 3.93/1.02      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
% 3.93/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_745,plain,
% 3.93/1.02      ( sP0(X0_52,X1_52,X0_51,X2_52,X3_52)
% 3.93/1.02      | ~ v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),X1_52,X0_52)
% 3.93/1.02      | ~ v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),X2_52,X0_52)
% 3.93/1.02      | ~ v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),u1_struct_0(X1_52),u1_struct_0(X0_52))
% 3.93/1.02      | ~ v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),u1_struct_0(X2_52),u1_struct_0(X0_52))
% 3.93/1.02      | ~ m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52))))
% 3.93/1.02      | ~ m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X0_52))))
% 3.93/1.02      | ~ v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51))
% 3.93/1.02      | ~ v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51)) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_9]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1520,plain,
% 3.93/1.02      ( sP0(X0_52,X1_52,X0_51,X2_52,X3_52) = iProver_top
% 3.93/1.02      | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),X1_52,X0_52) != iProver_top
% 3.93/1.02      | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),X2_52,X0_52) != iProver_top
% 3.93/1.02      | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 3.93/1.02      | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),u1_struct_0(X2_52),u1_struct_0(X0_52)) != iProver_top
% 3.93/1.02      | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 3.93/1.02      | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X0_52)))) != iProver_top
% 3.93/1.02      | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51)) != iProver_top
% 3.93/1.02      | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51)) != iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_745]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_9166,plain,
% 3.93/1.02      ( sP0(X0_52,sK6,X0_51,sK5,sK2) = iProver_top
% 3.93/1.02      | v5_pre_topc(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK5,X0_51),sK5,X0_52) != iProver_top
% 3.93/1.02      | v5_pre_topc(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK6,X0_51),sK6,X0_52) != iProver_top
% 3.93/1.02      | v1_funct_2(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK5,X0_51),u1_struct_0(sK5),u1_struct_0(X0_52)) != iProver_top
% 3.93/1.02      | v1_funct_2(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK6,X0_51),u1_struct_0(sK6),u1_struct_0(X0_52)) != iProver_top
% 3.93/1.02      | m1_subset_1(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK5,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_52)))) != iProver_top
% 3.93/1.02      | m1_subset_1(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_52)))) != iProver_top
% 3.93/1.02      | v1_funct_1(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK5,X0_51)) != iProver_top
% 3.93/1.02      | v1_funct_1(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK6,X0_51)) != iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_726,c_1520]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_9176,plain,
% 3.93/1.02      ( sP0(X0_52,sK6,X0_51,sK5,sK2) = iProver_top
% 3.93/1.02      | v5_pre_topc(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_51),sK5,X0_52) != iProver_top
% 3.93/1.02      | v5_pre_topc(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_51),sK6,X0_52) != iProver_top
% 3.93/1.02      | v1_funct_2(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_51),u1_struct_0(sK5),u1_struct_0(X0_52)) != iProver_top
% 3.93/1.02      | v1_funct_2(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_51),u1_struct_0(sK6),u1_struct_0(X0_52)) != iProver_top
% 3.93/1.02      | m1_subset_1(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_52)))) != iProver_top
% 3.93/1.02      | m1_subset_1(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_52)))) != iProver_top
% 3.93/1.02      | v1_funct_1(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_51)) != iProver_top
% 3.93/1.02      | v1_funct_1(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_51)) != iProver_top ),
% 3.93/1.02      inference(light_normalisation,[status(thm)],[c_9166,c_726]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_9367,plain,
% 3.93/1.02      ( sP0(sK3,sK6,sK4,sK5,sK2) = iProver_top
% 3.93/1.02      | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,sK4),sK5,sK3) != iProver_top
% 3.93/1.02      | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK6,sK4),sK6,sK3) != iProver_top
% 3.93/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,sK4),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.93/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK6,sK4),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 3.93/1.02      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.93/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 3.93/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,sK4)) != iProver_top
% 3.93/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK6,sK4)) != iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_5017,c_9176]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_723,negated_conjecture,
% 3.93/1.02      ( m1_pre_topc(sK5,sK2) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_56]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1541,plain,
% 3.93/1.02      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_723]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2946,plain,
% 3.93/1.02      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK5)) = k3_tmap_1(sK2,sK3,sK2,sK5,sK4)
% 3.93/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.93/1.02      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.93/1.02      | v2_struct_0(sK2) = iProver_top
% 3.93/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.93/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_1541,c_2933]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2864,plain,
% 3.93/1.02      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK5)) = k2_tmap_1(sK2,sK3,sK4,sK5) ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_1541,c_2856]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2953,plain,
% 3.93/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,sK4) = k2_tmap_1(sK2,sK3,sK4,sK5)
% 3.93/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.93/1.02      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.93/1.02      | v2_struct_0(sK2) = iProver_top
% 3.93/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.93/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 3.93/1.02      inference(light_normalisation,[status(thm)],[c_2946,c_2864]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_4920,plain,
% 3.93/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,sK4) = k2_tmap_1(sK2,sK3,sK4,sK5) ),
% 3.93/1.02      inference(global_propositional_subsumption,
% 3.93/1.02                [status(thm)],
% 3.93/1.02                [c_2953,c_67,c_68,c_69,c_76,c_77,c_78,c_79,c_3396]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_9377,plain,
% 3.93/1.02      ( sP0(sK3,sK6,sK4,sK5,sK2) = iProver_top
% 3.93/1.02      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 3.93/1.02      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 3.93/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.93/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 3.93/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.93/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 3.93/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 3.93/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 3.93/1.02      inference(light_normalisation,[status(thm)],[c_9367,c_4920,c_5017]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_8,plain,
% 3.93/1.02      ( ~ sP1(X0,X1,X2,X3,X4)
% 3.93/1.02      | sP0(X4,X3,X2,X1,X0)
% 3.93/1.02      | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
% 3.93/1.02      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 3.93/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 3.93/1.02      | ~ v1_funct_1(X2) ),
% 3.93/1.02      inference(cnf_transformation,[],[f39]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_746,plain,
% 3.93/1.02      ( ~ sP1(X0_52,X1_52,X0_51,X2_52,X3_52)
% 3.93/1.02      | sP0(X3_52,X2_52,X0_51,X1_52,X0_52)
% 3.93/1.02      | ~ v5_pre_topc(X0_51,k1_tsep_1(X0_52,X1_52,X2_52),X3_52)
% 3.93/1.02      | ~ v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))
% 3.93/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))))
% 3.93/1.02      | ~ v1_funct_1(X0_51) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_8]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1519,plain,
% 3.93/1.02      ( sP1(X0_52,X1_52,X0_51,X2_52,X3_52) != iProver_top
% 3.93/1.02      | sP0(X3_52,X2_52,X0_51,X1_52,X0_52) = iProver_top
% 3.93/1.02      | v5_pre_topc(X0_51,k1_tsep_1(X0_52,X1_52,X2_52),X3_52) != iProver_top
% 3.93/1.02      | v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52)) != iProver_top
% 3.93/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52)))) != iProver_top
% 3.93/1.02      | v1_funct_1(X0_51) != iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_746]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_8204,plain,
% 3.93/1.02      ( sP1(sK2,sK5,X0_51,sK6,X0_52) != iProver_top
% 3.93/1.02      | sP0(X0_52,sK6,X0_51,sK5,sK2) = iProver_top
% 3.93/1.02      | v5_pre_topc(X0_51,k1_tsep_1(sK2,sK5,sK6),X0_52) != iProver_top
% 3.93/1.02      | v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_52)) != iProver_top
% 3.93/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 3.93/1.02      | v1_funct_1(X0_51) != iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_726,c_1519]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_8211,plain,
% 3.93/1.02      ( sP1(sK2,sK5,X0_51,sK6,X0_52) != iProver_top
% 3.93/1.02      | sP0(X0_52,sK6,X0_51,sK5,sK2) = iProver_top
% 3.93/1.02      | v5_pre_topc(X0_51,sK2,X0_52) != iProver_top
% 3.93/1.02      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 3.93/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 3.93/1.02      | v1_funct_1(X0_51) != iProver_top ),
% 3.93/1.02      inference(light_normalisation,[status(thm)],[c_8204,c_726]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_8258,plain,
% 3.93/1.02      ( sP1(sK2,sK5,sK4,sK6,sK3) != iProver_top
% 3.93/1.02      | sP0(sK3,sK6,sK4,sK5,sK2) = iProver_top
% 3.93/1.02      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 3.93/1.02      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.93/1.02      | v1_funct_1(sK4) != iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_1543,c_8211]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_75,plain,
% 3.93/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_52,negated_conjecture,
% 3.93/1.02      ( r4_tsep_1(sK2,sK5,sK6) ),
% 3.93/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_80,plain,
% 3.93/1.02      ( r4_tsep_1(sK2,sK5,sK6) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_14,plain,
% 3.93/1.02      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.93/1.02      | m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ),
% 3.93/1.02      inference(cnf_transformation,[],[f47]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_740,plain,
% 3.93/1.02      ( ~ sP0(X0_52,X1_52,X0_51,X2_52,X3_52)
% 3.93/1.02      | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X0_52)))) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_14]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1525,plain,
% 3.93/1.02      ( sP0(X0_52,X1_52,X0_51,X2_52,X3_52) != iProver_top
% 3.93/1.02      | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X0_52)))) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_740]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_6998,plain,
% 3.93/1.02      ( sP0(X0_52,sK6,X0_51,sK5,sK2) != iProver_top
% 3.93/1.02      | m1_subset_1(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_52)))) = iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_726,c_1525]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_7157,plain,
% 3.93/1.02      ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
% 3.93/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_4920,c_6998]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_19,negated_conjecture,
% 3.93/1.02      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 3.93/1.02      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 3.93/1.02      | ~ v5_pre_topc(sK4,sK2,sK3)
% 3.93/1.02      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.93/1.02      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 3.93/1.02      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.93/1.02      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.93/1.02      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 3.93/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.93/1.02      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 3.93/1.02      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 3.93/1.02      | ~ v1_funct_1(sK4) ),
% 3.93/1.02      inference(cnf_transformation,[],[f101]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_482,plain,
% 3.93/1.02      ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 3.93/1.02      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 3.93/1.02      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 3.93/1.02      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.93/1.02      | ~ v5_pre_topc(sK4,sK2,sK3)
% 3.93/1.02      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 3.93/1.02      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 3.93/1.02      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.93/1.02      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 3.93/1.02      inference(global_propositional_subsumption,
% 3.93/1.02                [status(thm)],
% 3.93/1.02                [c_19,c_60,c_59,c_58]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_483,negated_conjecture,
% 3.93/1.02      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 3.93/1.02      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 3.93/1.02      | ~ v5_pre_topc(sK4,sK2,sK3)
% 3.93/1.02      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.93/1.02      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 3.93/1.02      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.93/1.02      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 3.93/1.02      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 3.93/1.02      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 3.93/1.02      inference(renaming,[status(thm)],[c_482]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_712,negated_conjecture,
% 3.93/1.02      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 3.93/1.02      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 3.93/1.02      | ~ v5_pre_topc(sK4,sK2,sK3)
% 3.93/1.02      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.93/1.02      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 3.93/1.02      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.93/1.02      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 3.93/1.02      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 3.93/1.02      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_483]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1552,plain,
% 3.93/1.02      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 3.93/1.02      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 3.93/1.02      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 3.93/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.93/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 3.93/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.93/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 3.93/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 3.93/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_712]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_7388,plain,
% 3.93/1.02      ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
% 3.93/1.02      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 3.93/1.02      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 3.93/1.02      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 3.93/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.93/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 3.93/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 3.93/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 3.93/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_7157,c_1552]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_484,plain,
% 3.93/1.02      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 3.93/1.02      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 3.93/1.02      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 3.93/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.93/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 3.93/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.93/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 3.93/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 3.93/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_15,plain,
% 3.93/1.02      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.93/1.02      | v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) ),
% 3.93/1.02      inference(cnf_transformation,[],[f46]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_739,plain,
% 3.93/1.02      ( ~ sP0(X0_52,X1_52,X0_51,X2_52,X3_52)
% 3.93/1.02      | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),X2_52,X0_52) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_15]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1526,plain,
% 3.93/1.02      ( sP0(X0_52,X1_52,X0_51,X2_52,X3_52) != iProver_top
% 3.93/1.02      | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),X2_52,X0_52) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_739]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_4728,plain,
% 3.93/1.02      ( sP0(X0_52,sK6,X0_51,sK5,sK2) != iProver_top
% 3.93/1.02      | v5_pre_topc(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_51),sK5,X0_52) = iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_726,c_1526]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_4923,plain,
% 3.93/1.02      ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
% 3.93/1.02      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_4920,c_4728]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_17,plain,
% 3.93/1.02      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.93/1.02      | v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
% 3.93/1.02      inference(cnf_transformation,[],[f44]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_737,plain,
% 3.93/1.02      ( ~ sP0(X0_52,X1_52,X0_51,X2_52,X3_52)
% 3.93/1.02      | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51)) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_17]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1528,plain,
% 3.93/1.02      ( sP0(X0_52,X1_52,X0_51,X2_52,X3_52) != iProver_top
% 3.93/1.02      | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51)) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_3681,plain,
% 3.93/1.02      ( sP0(X0_52,sK6,X0_51,sK5,sK2) != iProver_top
% 3.93/1.02      | v1_funct_1(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_51)) = iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_726,c_1528]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_4924,plain,
% 3.93/1.02      ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
% 3.93/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_4920,c_3681]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_11,plain,
% 3.93/1.02      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.93/1.02      | v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) ),
% 3.93/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_743,plain,
% 3.93/1.02      ( ~ sP0(X0_52,X1_52,X0_51,X2_52,X3_52)
% 3.93/1.02      | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),X1_52,X0_52) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_11]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1522,plain,
% 3.93/1.02      ( sP0(X0_52,X1_52,X0_51,X2_52,X3_52) != iProver_top
% 3.93/1.02      | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),X1_52,X0_52) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_743]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_4612,plain,
% 3.93/1.02      ( sP0(X0_52,sK6,X0_51,sK5,sK2) != iProver_top
% 3.93/1.02      | v5_pre_topc(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_51),sK6,X0_52) = iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_726,c_1522]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_5020,plain,
% 3.93/1.02      ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
% 3.93/1.02      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_5017,c_4612]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_13,plain,
% 3.93/1.02      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.93/1.02      | v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) ),
% 3.93/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_741,plain,
% 3.93/1.02      ( ~ sP0(X0_52,X1_52,X0_51,X2_52,X3_52)
% 3.93/1.02      | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51)) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_13]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1524,plain,
% 3.93/1.02      ( sP0(X0_52,X1_52,X0_51,X2_52,X3_52) != iProver_top
% 3.93/1.02      | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51)) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_3527,plain,
% 3.93/1.02      ( sP0(X0_52,sK6,X0_51,sK5,sK2) != iProver_top
% 3.93/1.02      | v1_funct_1(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_51)) = iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_726,c_1524]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_5021,plain,
% 3.93/1.02      ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
% 3.93/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_5017,c_3527]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_12,plain,
% 3.93/1.02      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.93/1.02      | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) ),
% 3.93/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_742,plain,
% 3.93/1.02      ( ~ sP0(X0_52,X1_52,X0_51,X2_52,X3_52)
% 3.93/1.02      | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),u1_struct_0(X1_52),u1_struct_0(X0_52)) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_12]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1523,plain,
% 3.93/1.02      ( sP0(X0_52,X1_52,X0_51,X2_52,X3_52) != iProver_top
% 3.93/1.02      | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),u1_struct_0(X1_52),u1_struct_0(X0_52)) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_742]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_5320,plain,
% 3.93/1.02      ( sP0(X0_52,sK6,X0_51,sK5,sK2) != iProver_top
% 3.93/1.02      | v1_funct_2(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_51),u1_struct_0(sK6),u1_struct_0(X0_52)) = iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_726,c_1523]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_5575,plain,
% 3.93/1.02      ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
% 3.93/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_5017,c_5320]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_16,plain,
% 3.93/1.02      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.93/1.02      | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) ),
% 3.93/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_738,plain,
% 3.93/1.02      ( ~ sP0(X0_52,X1_52,X0_51,X2_52,X3_52)
% 3.93/1.02      | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),u1_struct_0(X2_52),u1_struct_0(X0_52)) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_16]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1527,plain,
% 3.93/1.02      ( sP0(X0_52,X1_52,X0_51,X2_52,X3_52) != iProver_top
% 3.93/1.02      | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_51),u1_struct_0(X2_52),u1_struct_0(X0_52)) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_738]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_5580,plain,
% 3.93/1.02      ( sP0(X0_52,sK6,X0_51,sK5,sK2) != iProver_top
% 3.93/1.02      | v1_funct_2(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_51),u1_struct_0(sK5),u1_struct_0(X0_52)) = iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_726,c_1527]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_5688,plain,
% 3.93/1.02      ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
% 3.93/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_4920,c_5580]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_10,plain,
% 3.93/1.02      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.93/1.02      | m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
% 3.93/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_744,plain,
% 3.93/1.02      ( ~ sP0(X0_52,X1_52,X0_51,X2_52,X3_52)
% 3.93/1.02      | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_10]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1521,plain,
% 3.93/1.02      ( sP0(X0_52,X1_52,X0_51,X2_52,X3_52) != iProver_top
% 3.93/1.02      | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_6768,plain,
% 3.93/1.02      ( sP0(X0_52,sK6,X0_51,sK5,sK2) != iProver_top
% 3.93/1.02      | m1_subset_1(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_52)))) = iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_726,c_1521]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_6933,plain,
% 3.93/1.02      ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
% 3.93/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_5017,c_6768]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_7465,plain,
% 3.93/1.02      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 3.93/1.02      | sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top ),
% 3.93/1.02      inference(global_propositional_subsumption,
% 3.93/1.02                [status(thm)],
% 3.93/1.02                [c_7388,c_484,c_4923,c_4924,c_5020,c_5021,c_5575,c_5688,
% 3.93/1.02                 c_6933,c_7157]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_7466,plain,
% 3.93/1.02      ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
% 3.93/1.02      | v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
% 3.93/1.02      inference(renaming,[status(thm)],[c_7465]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_18,plain,
% 3.93/1.02      ( sP1(X0,X1,X2,X3,X4)
% 3.93/1.02      | ~ r4_tsep_1(X0,X1,X3)
% 3.93/1.02      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 3.93/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 3.93/1.02      | ~ m1_pre_topc(X3,X0)
% 3.93/1.02      | ~ m1_pre_topc(X1,X0)
% 3.93/1.02      | v2_struct_0(X0)
% 3.93/1.02      | v2_struct_0(X4)
% 3.93/1.02      | v2_struct_0(X1)
% 3.93/1.02      | v2_struct_0(X3)
% 3.93/1.02      | ~ v2_pre_topc(X4)
% 3.93/1.02      | ~ v2_pre_topc(X0)
% 3.93/1.02      | ~ l1_pre_topc(X4)
% 3.93/1.02      | ~ l1_pre_topc(X0)
% 3.93/1.02      | ~ v1_funct_1(X2) ),
% 3.93/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_736,plain,
% 3.93/1.02      ( sP1(X0_52,X1_52,X0_51,X2_52,X3_52)
% 3.93/1.02      | ~ r4_tsep_1(X0_52,X1_52,X2_52)
% 3.93/1.02      | ~ v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))
% 3.93/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))))
% 3.93/1.02      | ~ m1_pre_topc(X1_52,X0_52)
% 3.93/1.02      | ~ m1_pre_topc(X2_52,X0_52)
% 3.93/1.02      | v2_struct_0(X0_52)
% 3.93/1.02      | v2_struct_0(X1_52)
% 3.93/1.02      | v2_struct_0(X3_52)
% 3.93/1.02      | v2_struct_0(X2_52)
% 3.93/1.02      | ~ v2_pre_topc(X0_52)
% 3.93/1.02      | ~ v2_pre_topc(X3_52)
% 3.93/1.02      | ~ l1_pre_topc(X0_52)
% 3.93/1.02      | ~ l1_pre_topc(X3_52)
% 3.93/1.02      | ~ v1_funct_1(X0_51) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_18]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1529,plain,
% 3.93/1.02      ( sP1(X0_52,X1_52,X0_51,X2_52,X3_52) = iProver_top
% 3.93/1.02      | r4_tsep_1(X0_52,X1_52,X2_52) != iProver_top
% 3.93/1.02      | v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52)) != iProver_top
% 3.93/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52)))) != iProver_top
% 3.93/1.02      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 3.93/1.02      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 3.93/1.02      | v2_struct_0(X0_52) = iProver_top
% 3.93/1.02      | v2_struct_0(X1_52) = iProver_top
% 3.93/1.02      | v2_struct_0(X3_52) = iProver_top
% 3.93/1.02      | v2_struct_0(X2_52) = iProver_top
% 3.93/1.02      | v2_pre_topc(X0_52) != iProver_top
% 3.93/1.02      | v2_pre_topc(X3_52) != iProver_top
% 3.93/1.02      | l1_pre_topc(X0_52) != iProver_top
% 3.93/1.02      | l1_pre_topc(X3_52) != iProver_top
% 3.93/1.02      | v1_funct_1(X0_51) != iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_736]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_8342,plain,
% 3.93/1.02      ( sP1(sK2,sK5,X0_51,sK6,X0_52) = iProver_top
% 3.93/1.02      | r4_tsep_1(sK2,sK5,sK6) != iProver_top
% 3.93/1.02      | v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_52)) != iProver_top
% 3.93/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 3.93/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.93/1.02      | m1_pre_topc(sK6,sK2) != iProver_top
% 3.93/1.02      | v2_struct_0(X0_52) = iProver_top
% 3.93/1.02      | v2_struct_0(sK5) = iProver_top
% 3.93/1.02      | v2_struct_0(sK6) = iProver_top
% 3.93/1.02      | v2_struct_0(sK2) = iProver_top
% 3.93/1.02      | v2_pre_topc(X0_52) != iProver_top
% 3.93/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.93/1.02      | l1_pre_topc(X0_52) != iProver_top
% 3.93/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.93/1.02      | v1_funct_1(X0_51) != iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_726,c_1529]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_8358,plain,
% 3.93/1.02      ( sP1(sK2,sK5,X0_51,sK6,X0_52) = iProver_top
% 3.93/1.02      | r4_tsep_1(sK2,sK5,sK6) != iProver_top
% 3.93/1.02      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 3.93/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 3.93/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.93/1.02      | m1_pre_topc(sK6,sK2) != iProver_top
% 3.93/1.02      | v2_struct_0(X0_52) = iProver_top
% 3.93/1.02      | v2_struct_0(sK5) = iProver_top
% 3.93/1.02      | v2_struct_0(sK6) = iProver_top
% 3.93/1.02      | v2_struct_0(sK2) = iProver_top
% 3.93/1.02      | v2_pre_topc(X0_52) != iProver_top
% 3.93/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.93/1.02      | l1_pre_topc(X0_52) != iProver_top
% 3.93/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.93/1.02      | v1_funct_1(X0_51) != iProver_top ),
% 3.93/1.02      inference(light_normalisation,[status(thm)],[c_8342,c_726]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_8441,plain,
% 3.93/1.02      ( sP1(sK2,sK5,sK4,sK6,sK3) = iProver_top
% 3.93/1.02      | r4_tsep_1(sK2,sK5,sK6) != iProver_top
% 3.93/1.02      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.93/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.93/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.93/1.02      | m1_pre_topc(sK6,sK2) != iProver_top
% 3.93/1.02      | v2_struct_0(sK5) = iProver_top
% 3.93/1.02      | v2_struct_0(sK6) = iProver_top
% 3.93/1.02      | v2_struct_0(sK3) = iProver_top
% 3.93/1.02      | v2_struct_0(sK2) = iProver_top
% 3.93/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.93/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.93/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.93/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.93/1.02      | v1_funct_1(sK4) != iProver_top ),
% 3.93/1.02      inference(instantiation,[status(thm)],[c_8358]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_8626,plain,
% 3.93/1.02      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
% 3.93/1.02      inference(global_propositional_subsumption,
% 3.93/1.02                [status(thm)],
% 3.93/1.02                [c_8258,c_67,c_68,c_69,c_70,c_71,c_72,c_73,c_74,c_75,
% 3.93/1.02                 c_76,c_77,c_78,c_79,c_80,c_7466,c_8441]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_5,plain,
% 3.93/1.02      ( ~ sP1(X0,X1,X2,X3,X4)
% 3.93/1.02      | ~ sP0(X4,X3,X2,X1,X0)
% 3.93/1.02      | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
% 3.93/1.02      inference(cnf_transformation,[],[f42]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_749,plain,
% 3.93/1.02      ( ~ sP1(X0_52,X1_52,X0_51,X2_52,X3_52)
% 3.93/1.02      | ~ sP0(X3_52,X2_52,X0_51,X1_52,X0_52)
% 3.93/1.02      | v5_pre_topc(X0_51,k1_tsep_1(X0_52,X1_52,X2_52),X3_52) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_5]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1516,plain,
% 3.93/1.02      ( sP1(X0_52,X1_52,X0_51,X2_52,X3_52) != iProver_top
% 3.93/1.02      | sP0(X3_52,X2_52,X0_51,X1_52,X0_52) != iProver_top
% 3.93/1.02      | v5_pre_topc(X0_51,k1_tsep_1(X0_52,X1_52,X2_52),X3_52) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_749]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_6584,plain,
% 3.93/1.02      ( sP1(sK2,sK5,X0_51,sK6,X0_52) != iProver_top
% 3.93/1.02      | sP0(X0_52,sK6,X0_51,sK5,sK2) != iProver_top
% 3.93/1.02      | v5_pre_topc(X0_51,sK2,X0_52) = iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_726,c_1516]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_6586,plain,
% 3.93/1.02      ( sP1(sK2,sK5,sK4,sK6,sK3) != iProver_top
% 3.93/1.02      | sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
% 3.93/1.02      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 3.93/1.02      inference(instantiation,[status(thm)],[c_6584]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_21,negated_conjecture,
% 3.93/1.02      ( v5_pre_topc(sK4,sK2,sK3)
% 3.93/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 3.93/1.02      inference(cnf_transformation,[],[f99]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_111,plain,
% 3.93/1.02      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 3.93/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_25,negated_conjecture,
% 3.93/1.02      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 3.93/1.02      | v5_pre_topc(sK4,sK2,sK3) ),
% 3.93/1.02      inference(cnf_transformation,[],[f95]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_107,plain,
% 3.93/1.02      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
% 3.93/1.02      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_29,negated_conjecture,
% 3.93/1.02      ( v5_pre_topc(sK4,sK2,sK3)
% 3.93/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
% 3.93/1.02      inference(cnf_transformation,[],[f91]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_103,plain,
% 3.93/1.02      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 3.93/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_33,negated_conjecture,
% 3.93/1.02      ( v5_pre_topc(sK4,sK2,sK3)
% 3.93/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 3.93/1.02      inference(cnf_transformation,[],[f87]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_99,plain,
% 3.93/1.02      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 3.93/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_37,negated_conjecture,
% 3.93/1.02      ( v5_pre_topc(sK4,sK2,sK3)
% 3.93/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 3.93/1.02      inference(cnf_transformation,[],[f83]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_95,plain,
% 3.93/1.02      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 3.93/1.02      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_41,negated_conjecture,
% 3.93/1.02      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 3.93/1.02      | v5_pre_topc(sK4,sK2,sK3) ),
% 3.93/1.02      inference(cnf_transformation,[],[f79]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_91,plain,
% 3.93/1.02      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
% 3.93/1.02      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_45,negated_conjecture,
% 3.93/1.02      ( v5_pre_topc(sK4,sK2,sK3)
% 3.93/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 3.93/1.02      inference(cnf_transformation,[],[f75]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_87,plain,
% 3.93/1.02      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 3.93/1.02      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_49,negated_conjecture,
% 3.93/1.02      ( v5_pre_topc(sK4,sK2,sK3)
% 3.93/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
% 3.93/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_83,plain,
% 3.93/1.02      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 3.93/1.02      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(contradiction,plain,
% 3.93/1.02      ( $false ),
% 3.93/1.02      inference(minisat,
% 3.93/1.02                [status(thm)],
% 3.93/1.02                [c_9377,c_8626,c_8441,c_6586,c_111,c_107,c_103,c_99,c_95,
% 3.93/1.02                 c_91,c_87,c_83,c_80,c_79,c_78,c_77,c_76,c_75,c_74,c_73,
% 3.93/1.02                 c_72,c_71,c_70,c_69,c_68,c_67]) ).
% 3.93/1.02  
% 3.93/1.02  
% 3.93/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.93/1.02  
% 3.93/1.02  ------                               Statistics
% 3.93/1.02  
% 3.93/1.02  ------ Selected
% 3.93/1.02  
% 3.93/1.02  total_time:                             0.335
% 3.93/1.02  
%------------------------------------------------------------------------------
