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
% DateTime   : Thu Dec  3 12:24:21 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  241 (4650 expanded)
%              Number of clauses        :  165 ( 888 expanded)
%              Number of leaves         :   20 (1706 expanded)
%              Depth                    :   20
%              Number of atoms          : 1640 (162050 expanded)
%              Number of equality atoms :  330 (6156 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   80 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
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
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & v1_tsep_1(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( k1_tsep_1(X0,X3,X4) = X0
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

fof(f7,negated_conjecture,(
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
                      & v1_tsep_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & v1_tsep_1(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( k1_tsep_1(X0,X3,X4) = X0
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
    inference(negated_conjecture,[],[f6])).

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
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
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
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
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
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
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
    inference(flattening,[],[f17])).

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
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
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
    inference(nnf_transformation,[],[f18])).

fof(f29,plain,(
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
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
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
    inference(flattening,[],[f28])).

fof(f34,plain,(
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
          & k1_tsep_1(X0,X3,X4) = X0
          & m1_pre_topc(X4,X0)
          & v1_tsep_1(X4,X0)
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
        & k1_tsep_1(X0,X3,sK6) = X0
        & m1_pre_topc(sK6,X0)
        & v1_tsep_1(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
              & k1_tsep_1(X0,X3,X4) = X0
              & m1_pre_topc(X4,X0)
              & v1_tsep_1(X4,X0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,X0)
          & v1_tsep_1(X3,X0)
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
            & k1_tsep_1(X0,sK5,X4) = X0
            & m1_pre_topc(X4,X0)
            & v1_tsep_1(X4,X0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(sK5,X0)
        & v1_tsep_1(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
                  & k1_tsep_1(X0,X3,X4) = X0
                  & m1_pre_topc(X4,X0)
                  & v1_tsep_1(X4,X0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,X0)
              & v1_tsep_1(X3,X0)
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
                & k1_tsep_1(X0,X3,X4) = X0
                & m1_pre_topc(X4,X0)
                & v1_tsep_1(X4,X0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,X0)
            & v1_tsep_1(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
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
                    & k1_tsep_1(X0,X3,X4) = X0
                    & m1_pre_topc(X4,X0)
                    & v1_tsep_1(X4,X0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,X0)
                & v1_tsep_1(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
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
                        & k1_tsep_1(X0,X3,X4) = X0
                        & m1_pre_topc(X4,X0)
                        & v1_tsep_1(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
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
                      & k1_tsep_1(sK2,X3,X4) = sK2
                      & m1_pre_topc(X4,sK2)
                      & v1_tsep_1(X4,sK2)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK2)
                  & v1_tsep_1(X3,sK2)
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

fof(f35,plain,
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
    & k1_tsep_1(sK2,sK5,sK6) = sK2
    & m1_pre_topc(sK6,sK2)
    & v1_tsep_1(sK6,sK2)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK2)
    & v1_tsep_1(sK5,sK2)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f29,f34,f33,f32,f31,f30])).

fof(f69,plain,(
    m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f37,plain,(
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

fof(f58,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f36,plain,(
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

fof(f55,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f70,plain,(
    k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f35])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f20,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
      <=> sP0(X1,X3,X4,X2,X0) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

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
    inference(nnf_transformation,[],[f20])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
      | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(X2)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f103,plain,
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
    inference(cnf_transformation,[],[f35])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
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

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f21,plain,(
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
    inference(definition_folding,[],[f13,f20,f19])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0) )
             => r4_tsep_1(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f101,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f97,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f93,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f89,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    v1_tsep_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f67,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    v1_tsep_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f64,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2140,plain,
    ( ~ m1_subset_1(X0_53,X0_55)
    | m1_subset_1(X1_53,X1_55)
    | X1_55 != X0_55
    | X1_53 != X0_53 ),
    theory(equality)).

cnf(c_3721,plain,
    ( m1_subset_1(X0_53,X0_55)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | X0_55 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | X0_53 != X1_53 ),
    inference(instantiation,[status(thm)],[c_2140])).

cnf(c_7591,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | X0_53 != X1_53 ),
    inference(instantiation,[status(thm)],[c_3721])).

cnf(c_7594,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_7591])).

cnf(c_53,negated_conjecture,
    ( m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2099,negated_conjecture,
    ( m1_pre_topc(sK6,sK2) ),
    inference(subtyping,[status(esa)],[c_53])).

cnf(c_2960,plain,
    ( m1_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2099])).

cnf(c_59,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2093,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_59])).

cnf(c_2966,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2093])).

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
    inference(cnf_transformation,[],[f37])).

cnf(c_2124,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ m1_pre_topc(X2_52,X0_52)
    | ~ m1_pre_topc(X2_52,X3_52)
    | ~ m1_pre_topc(X0_52,X3_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X3_52)
    | ~ v2_pre_topc(X3_52)
    | ~ v2_pre_topc(X1_52)
    | ~ l1_pre_topc(X3_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2936,plain,
    ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53)
    | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_pre_topc(X2_52,X3_52) != iProver_top
    | m1_pre_topc(X0_52,X3_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X3_52) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X3_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X3_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2124])).

cnf(c_3795,plain,
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
    inference(superposition,[status(thm)],[c_2966,c_2936])).

cnf(c_64,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_71,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64])).

cnf(c_63,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_72,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63])).

cnf(c_62,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_73,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_61,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_74,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_60,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_75,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_4116,plain,
    ( v2_pre_topc(X1_52) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK3,sK2,X0_52,sK4)
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(X0_52,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3795,c_71,c_72,c_73,c_74,c_75])).

cnf(c_4117,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK3,sK2,X0_52,sK4)
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(X0_52,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_4116])).

cnf(c_4129,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK6)) = k3_tmap_1(sK2,sK3,sK2,sK6,sK4)
    | m1_pre_topc(sK6,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2960,c_4117])).

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
    inference(cnf_transformation,[],[f36])).

cnf(c_2125,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ m1_pre_topc(X2_52,X0_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(X1_52)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_53,X2_52) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2935,plain,
    ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_53,X2_52)
    | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2125])).

cnf(c_3633,plain,
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
    inference(superposition,[status(thm)],[c_2966,c_2935])).

cnf(c_67,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_68,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_67])).

cnf(c_66,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_69,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66])).

cnf(c_65,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_70,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65])).

cnf(c_4023,plain,
    ( m1_pre_topc(X0_52,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK2,sK3,sK4,X0_52) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3633,c_68,c_69,c_70,c_71,c_72,c_73,c_74,c_75])).

cnf(c_4024,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK2,sK3,sK4,X0_52)
    | m1_pre_topc(X0_52,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4023])).

cnf(c_4031,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK6)) = k2_tmap_1(sK2,sK3,sK4,sK6) ),
    inference(superposition,[status(thm)],[c_2960,c_4024])).

cnf(c_4163,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK6,sK4) = k2_tmap_1(sK2,sK3,sK4,sK6)
    | m1_pre_topc(sK6,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4129,c_4031])).

cnf(c_82,plain,
    ( m1_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_17,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2109,plain,
    ( m1_pre_topc(X0_52,X0_52)
    | ~ l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_3436,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2109])).

cnf(c_3439,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3436])).

cnf(c_5858,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK6,sK4) = k2_tmap_1(sK2,sK3,sK4,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4163,c_68,c_69,c_70,c_82,c_3439])).

cnf(c_52,negated_conjecture,
    ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2100,negated_conjecture,
    ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(subtyping,[status(esa)],[c_52])).

cnf(c_7,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2118,plain,
    ( sP0(X0_52,X1_52,X0_53,X2_52,X3_52)
    | ~ v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),X1_52,X0_52)
    | ~ v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),X2_52,X0_52)
    | ~ v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),u1_struct_0(X1_52),u1_struct_0(X0_52))
    | ~ v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),u1_struct_0(X2_52),u1_struct_0(X0_52))
    | ~ m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52))))
    | ~ m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X0_52))))
    | ~ v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53))
    | ~ v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2942,plain,
    ( sP0(X0_52,X1_52,X0_53,X2_52,X3_52) = iProver_top
    | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),X1_52,X0_52) != iProver_top
    | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),X2_52,X0_52) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),u1_struct_0(X2_52),u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X0_52)))) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53)) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2118])).

cnf(c_7106,plain,
    ( sP0(X0_52,sK6,X0_53,sK5,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK5,X0_53),sK5,X0_52) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK6,X0_53),sK6,X0_52) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK6,X0_53),u1_struct_0(sK6),u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_52)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK5,X0_53)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK6,X0_53)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_2942])).

cnf(c_7116,plain,
    ( sP0(X0_52,sK6,X0_53,sK5,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_53),sK5,X0_52) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_53),sK6,X0_52) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_53),u1_struct_0(sK6),u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_52)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_53)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_53)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7106,c_2100])).

cnf(c_7186,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,sK4),sK5,sK3) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK6,sK4),sK6,sK3) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,sK4),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK6,sK4),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,sK4)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK6,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5858,c_7116])).

cnf(c_56,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2096,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(subtyping,[status(esa)],[c_56])).

cnf(c_2963,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2096])).

cnf(c_4130,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK5)) = k3_tmap_1(sK2,sK3,sK2,sK5,sK4)
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2963,c_4117])).

cnf(c_4032,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK5)) = k2_tmap_1(sK2,sK3,sK4,sK5) ),
    inference(superposition,[status(thm)],[c_2963,c_4024])).

cnf(c_4150,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,sK4) = k2_tmap_1(sK2,sK3,sK4,sK5)
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4130,c_4032])).

cnf(c_79,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_5408,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,sK4) = k2_tmap_1(sK2,sK3,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4150,c_68,c_69,c_70,c_79,c_3439])).

cnf(c_7196,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7186,c_5408,c_5858])).

cnf(c_7206,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7196])).

cnf(c_6,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | sP0(X4,X3,X2,X1,X0)
    | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2119,plain,
    ( ~ sP1(X0_52,X1_52,X0_53,X2_52,X3_52)
    | sP0(X3_52,X2_52,X0_53,X1_52,X0_52)
    | ~ v5_pre_topc(X0_53,k1_tsep_1(X0_52,X1_52,X2_52),X3_52)
    | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))))
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2941,plain,
    ( sP1(X0_52,X1_52,X0_53,X2_52,X3_52) != iProver_top
    | sP0(X3_52,X2_52,X0_53,X1_52,X0_52) = iProver_top
    | v5_pre_topc(X0_53,k1_tsep_1(X0_52,X1_52,X2_52),X3_52) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2119])).

cnf(c_6072,plain,
    ( sP1(sK2,sK5,X0_53,sK6,X0_52) != iProver_top
    | sP0(X0_52,sK6,X0_53,sK5,sK2) = iProver_top
    | v5_pre_topc(X0_53,k1_tsep_1(sK2,sK5,sK6),X0_52) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_2941])).

cnf(c_6079,plain,
    ( sP1(sK2,sK5,X0_53,sK6,X0_52) != iProver_top
    | sP0(X0_52,sK6,X0_53,sK5,sK2) = iProver_top
    | v5_pre_topc(X0_53,sK2,X0_52) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6072,c_2100])).

cnf(c_6604,plain,
    ( sP1(sK2,sK5,sK4,sK6,sK3) != iProver_top
    | sP0(sK3,sK6,sK4,sK5,sK2) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2966,c_6079])).

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
    inference(cnf_transformation,[],[f103])).

cnf(c_443,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_61,c_60,c_59])).

cnf(c_444,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(renaming,[status(thm)],[c_443])).

cnf(c_445,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2112,plain,
    ( ~ sP0(X0_52,X1_52,X0_53,X2_52,X3_52)
    | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),X2_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2948,plain,
    ( sP0(X0_52,X1_52,X0_53,X2_52,X3_52) != iProver_top
    | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),X2_52,X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2112])).

cnf(c_5154,plain,
    ( sP0(X0_52,sK6,X0_53,sK5,sK2) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_53),sK5,X0_52) = iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_2948])).

cnf(c_5411,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5408,c_5154])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2110,plain,
    ( ~ sP0(X0_52,X1_52,X0_53,X2_52,X3_52)
    | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2950,plain,
    ( sP0(X0_52,X1_52,X0_53,X2_52,X3_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2110])).

cnf(c_4486,plain,
    ( sP0(X0_52,sK6,X0_53,sK5,sK2) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_53)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_2950])).

cnf(c_5412,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5408,c_4486])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2111,plain,
    ( ~ sP0(X0_52,X1_52,X0_53,X2_52,X3_52)
    | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),u1_struct_0(X2_52),u1_struct_0(X0_52)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2949,plain,
    ( sP0(X0_52,X1_52,X0_53,X2_52,X3_52) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),u1_struct_0(X2_52),u1_struct_0(X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2111])).

cnf(c_5604,plain,
    ( sP0(X0_52,sK6,X0_53,sK5,sK2) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_52)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_2949])).

cnf(c_5714,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5408,c_5604])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2115,plain,
    ( ~ sP0(X0_52,X1_52,X0_53,X2_52,X3_52)
    | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),u1_struct_0(X1_52),u1_struct_0(X0_52)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2945,plain,
    ( sP0(X0_52,X1_52,X0_53,X2_52,X3_52) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),u1_struct_0(X1_52),u1_struct_0(X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2115])).

cnf(c_5509,plain,
    ( sP0(X0_52,sK6,X0_53,sK5,sK2) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_53),u1_struct_0(sK6),u1_struct_0(X0_52)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_2945])).

cnf(c_5861,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5858,c_5509])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2116,plain,
    ( ~ sP0(X0_52,X1_52,X0_53,X2_52,X3_52)
    | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),X1_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2944,plain,
    ( sP0(X0_52,X1_52,X0_53,X2_52,X3_52) != iProver_top
    | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),X1_52,X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2116])).

cnf(c_5104,plain,
    ( sP0(X0_52,sK6,X0_53,sK5,sK2) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_53),sK6,X0_52) = iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_2944])).

cnf(c_5862,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5858,c_5104])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2114,plain,
    ( ~ sP0(X0_52,X1_52,X0_53,X2_52,X3_52)
    | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2946,plain,
    ( sP0(X0_52,X1_52,X0_53,X2_52,X3_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2114])).

cnf(c_4430,plain,
    ( sP0(X0_52,sK6,X0_53,sK5,sK2) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_53)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_2946])).

cnf(c_5863,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5858,c_4430])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2117,plain,
    ( ~ sP0(X0_52,X1_52,X0_53,X2_52,X3_52)
    | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2943,plain,
    ( sP0(X0_52,X1_52,X0_53,X2_52,X3_52) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2117])).

cnf(c_6147,plain,
    ( sP0(X0_52,sK6,X0_53,sK5,sK2) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_52)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_2943])).

cnf(c_6230,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5858,c_6147])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2113,plain,
    ( ~ sP0(X0_52,X1_52,X0_53,X2_52,X3_52)
    | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X0_52)))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2947,plain,
    ( sP0(X0_52,X1_52,X0_53,X2_52,X3_52) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X0_52)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2113])).

cnf(c_6341,plain,
    ( sP0(X0_52,sK6,X0_53,sK5,sK2) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_52)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_2947])).

cnf(c_6420,plain,
    ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5408,c_6341])).

cnf(c_6878,plain,
    ( sP1(sK2,sK5,sK4,sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6604,c_74,c_75,c_445,c_5411,c_5412,c_5714,c_5861,c_5862,c_5863,c_6230,c_6420])).

cnf(c_6880,plain,
    ( ~ sP1(sK2,sK5,sK4,sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6878])).

cnf(c_2139,plain,
    ( X0_56 != X1_56
    | k1_zfmisc_1(X0_56) = k1_zfmisc_1(X1_56) ),
    theory(equality)).

cnf(c_3451,plain,
    ( X0_56 != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))
    | k1_zfmisc_1(X0_56) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_2139])).

cnf(c_3725,plain,
    ( k2_zfmisc_1(X0_54,X1_54) != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))
    | k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_3451])).

cnf(c_5609,plain,
    ( k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_3725])).

cnf(c_2138,plain,
    ( k2_zfmisc_1(X0_54,X1_54) = k2_zfmisc_1(X2_54,X3_54)
    | X0_54 != X2_54
    | X1_54 != X3_54 ),
    theory(equality)).

cnf(c_3726,plain,
    ( k2_zfmisc_1(X0_54,X1_54) = k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))
    | X1_54 != u1_struct_0(sK3)
    | X0_54 != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2138])).

cnf(c_4316,plain,
    ( k2_zfmisc_1(X0_54,u1_struct_0(sK3)) = k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))
    | X0_54 != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3726])).

cnf(c_5123,plain,
    ( k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) = k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))
    | u1_struct_0(k1_tsep_1(sK2,sK5,sK6)) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4316])).

cnf(c_3,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2122,plain,
    ( ~ sP1(X0_52,X1_52,X0_53,X2_52,X3_52)
    | ~ sP0(X3_52,X2_52,X0_53,X1_52,X0_52)
    | v5_pre_topc(X0_53,k1_tsep_1(X0_52,X1_52,X2_52),X3_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2938,plain,
    ( sP1(X0_52,X1_52,X0_53,X2_52,X3_52) != iProver_top
    | sP0(X3_52,X2_52,X0_53,X1_52,X0_52) != iProver_top
    | v5_pre_topc(X0_53,k1_tsep_1(X0_52,X1_52,X2_52),X3_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2122])).

cnf(c_5050,plain,
    ( sP1(sK2,sK5,X0_53,sK6,X0_52) != iProver_top
    | sP0(X0_52,sK6,X0_53,sK5,sK2) != iProver_top
    | v5_pre_topc(X0_53,sK2,X0_52) = iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_2938])).

cnf(c_5051,plain,
    ( ~ sP1(sK2,sK5,X0_53,sK6,X0_52)
    | ~ sP0(X0_52,sK6,X0_53,sK5,sK2)
    | v5_pre_topc(X0_53,sK2,X0_52) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5050])).

cnf(c_5053,plain,
    ( ~ sP1(sK2,sK5,sK4,sK6,sK3)
    | ~ sP0(sK3,sK6,sK4,sK5,sK2)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_5051])).

cnf(c_2141,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | v1_funct_2(X1_53,X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54
    | X1_53 != X0_53 ),
    theory(equality)).

cnf(c_3362,plain,
    ( v1_funct_2(X0_53,X0_54,X1_54)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | X1_54 != u1_struct_0(sK3)
    | X0_54 != u1_struct_0(sK2)
    | X0_53 != sK4 ),
    inference(instantiation,[status(thm)],[c_2141])).

cnf(c_3483,plain,
    ( v1_funct_2(X0_53,X0_54,u1_struct_0(X0_52))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | X0_54 != u1_struct_0(sK2)
    | u1_struct_0(X0_52) != u1_struct_0(sK3)
    | X0_53 != sK4 ),
    inference(instantiation,[status(thm)],[c_3362])).

cnf(c_4502,plain,
    ( v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_52))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | u1_struct_0(X0_52) != u1_struct_0(sK3)
    | u1_struct_0(k1_tsep_1(sK2,sK5,sK6)) != u1_struct_0(sK2)
    | X0_53 != sK4 ),
    inference(instantiation,[status(thm)],[c_3483])).

cnf(c_4505,plain,
    ( v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | u1_struct_0(k1_tsep_1(sK2,sK5,sK6)) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4502])).

cnf(c_2135,plain,
    ( u1_struct_0(X0_52) = u1_struct_0(X1_52)
    | X0_52 != X1_52 ),
    theory(equality)).

cnf(c_3839,plain,
    ( u1_struct_0(X0_52) = u1_struct_0(sK2)
    | X0_52 != sK2 ),
    inference(instantiation,[status(thm)],[c_2135])).

cnf(c_4306,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK5,sK6)) = u1_struct_0(sK2)
    | k1_tsep_1(sK2,sK5,sK6) != sK2 ),
    inference(instantiation,[status(thm)],[c_3839])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f52])).

cnf(c_18,plain,
    ( r4_tsep_1(X0,X1,X2)
    | ~ v1_tsep_1(X2,X0)
    | ~ v1_tsep_1(X1,X0)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_674,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ v1_tsep_1(X5,X6)
    | ~ v1_tsep_1(X7,X6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_pre_topc(X5,X6)
    | ~ m1_pre_topc(X7,X6)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X6)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X6)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X6)
    | ~ v1_funct_1(X2)
    | X5 != X3
    | X7 != X1
    | X6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_675,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ v1_tsep_1(X1,X0)
    | ~ v1_tsep_1(X3,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X2) ),
    inference(unflattening,[status(thm)],[c_674])).

cnf(c_2083,plain,
    ( sP1(X0_52,X1_52,X0_53,X2_52,X3_52)
    | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))
    | ~ v1_tsep_1(X1_52,X0_52)
    | ~ v1_tsep_1(X2_52,X0_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))))
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
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_675])).

cnf(c_3405,plain,
    ( sP1(sK2,sK5,X0_53,X0_52,X1_52)
    | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK5,X0_52)),u1_struct_0(X1_52))
    | ~ v1_tsep_1(X0_52,sK2)
    | ~ v1_tsep_1(sK5,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,X0_52)),u1_struct_0(X1_52))))
    | ~ m1_pre_topc(X0_52,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(sK5)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0_53) ),
    inference(instantiation,[status(thm)],[c_2083])).

cnf(c_3521,plain,
    ( sP1(sK2,sK5,X0_53,sK6,X0_52)
    | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_52))
    | ~ v1_tsep_1(sK5,sK2)
    | ~ v1_tsep_1(sK6,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_52))))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(X0_52)
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0_53) ),
    inference(instantiation,[status(thm)],[c_3405])).

cnf(c_3523,plain,
    ( sP1(sK2,sK5,sK4,sK6,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
    | ~ v1_tsep_1(sK5,sK2)
    | ~ v1_tsep_1(sK6,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3521])).

cnf(c_2128,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_2168,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2128])).

cnf(c_2127,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_2167,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2127])).

cnf(c_2151,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2135])).

cnf(c_21,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_25,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_29,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_33,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_37,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_41,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_45,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_49,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_54,negated_conjecture,
    ( v1_tsep_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_55,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_57,negated_conjecture,
    ( v1_tsep_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_58,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f64])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7594,c_7206,c_6880,c_5609,c_5123,c_5053,c_4505,c_4306,c_3523,c_2100,c_2168,c_2167,c_2151,c_21,c_25,c_29,c_33,c_37,c_41,c_45,c_49,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_62,c_63,c_64,c_65,c_66,c_67])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:52:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.14/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/0.99  
% 3.14/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.14/0.99  
% 3.14/0.99  ------  iProver source info
% 3.14/0.99  
% 3.14/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.14/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.14/0.99  git: non_committed_changes: false
% 3.14/0.99  git: last_make_outside_of_git: false
% 3.14/0.99  
% 3.14/0.99  ------ 
% 3.14/0.99  
% 3.14/0.99  ------ Input Options
% 3.14/0.99  
% 3.14/0.99  --out_options                           all
% 3.14/0.99  --tptp_safe_out                         true
% 3.14/0.99  --problem_path                          ""
% 3.14/0.99  --include_path                          ""
% 3.14/0.99  --clausifier                            res/vclausify_rel
% 3.14/0.99  --clausifier_options                    --mode clausify
% 3.14/0.99  --stdin                                 false
% 3.14/0.99  --stats_out                             all
% 3.14/0.99  
% 3.14/0.99  ------ General Options
% 3.14/0.99  
% 3.14/0.99  --fof                                   false
% 3.14/0.99  --time_out_real                         305.
% 3.14/0.99  --time_out_virtual                      -1.
% 3.14/0.99  --symbol_type_check                     false
% 3.14/0.99  --clausify_out                          false
% 3.14/0.99  --sig_cnt_out                           false
% 3.14/0.99  --trig_cnt_out                          false
% 3.14/0.99  --trig_cnt_out_tolerance                1.
% 3.14/0.99  --trig_cnt_out_sk_spl                   false
% 3.14/0.99  --abstr_cl_out                          false
% 3.14/0.99  
% 3.14/0.99  ------ Global Options
% 3.14/0.99  
% 3.14/0.99  --schedule                              default
% 3.14/0.99  --add_important_lit                     false
% 3.14/0.99  --prop_solver_per_cl                    1000
% 3.14/0.99  --min_unsat_core                        false
% 3.14/0.99  --soft_assumptions                      false
% 3.14/0.99  --soft_lemma_size                       3
% 3.14/0.99  --prop_impl_unit_size                   0
% 3.14/0.99  --prop_impl_unit                        []
% 3.14/0.99  --share_sel_clauses                     true
% 3.14/0.99  --reset_solvers                         false
% 3.14/0.99  --bc_imp_inh                            [conj_cone]
% 3.14/0.99  --conj_cone_tolerance                   3.
% 3.14/0.99  --extra_neg_conj                        none
% 3.14/0.99  --large_theory_mode                     true
% 3.14/0.99  --prolific_symb_bound                   200
% 3.14/0.99  --lt_threshold                          2000
% 3.14/0.99  --clause_weak_htbl                      true
% 3.14/0.99  --gc_record_bc_elim                     false
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing Options
% 3.14/0.99  
% 3.14/0.99  --preprocessing_flag                    true
% 3.14/0.99  --time_out_prep_mult                    0.1
% 3.14/0.99  --splitting_mode                        input
% 3.14/0.99  --splitting_grd                         true
% 3.14/0.99  --splitting_cvd                         false
% 3.14/0.99  --splitting_cvd_svl                     false
% 3.14/0.99  --splitting_nvd                         32
% 3.14/0.99  --sub_typing                            true
% 3.14/0.99  --prep_gs_sim                           true
% 3.14/0.99  --prep_unflatten                        true
% 3.14/0.99  --prep_res_sim                          true
% 3.14/0.99  --prep_upred                            true
% 3.14/0.99  --prep_sem_filter                       exhaustive
% 3.14/0.99  --prep_sem_filter_out                   false
% 3.14/0.99  --pred_elim                             true
% 3.14/0.99  --res_sim_input                         true
% 3.14/0.99  --eq_ax_congr_red                       true
% 3.14/0.99  --pure_diseq_elim                       true
% 3.14/0.99  --brand_transform                       false
% 3.14/0.99  --non_eq_to_eq                          false
% 3.14/0.99  --prep_def_merge                        true
% 3.14/0.99  --prep_def_merge_prop_impl              false
% 3.14/0.99  --prep_def_merge_mbd                    true
% 3.14/0.99  --prep_def_merge_tr_red                 false
% 3.14/0.99  --prep_def_merge_tr_cl                  false
% 3.14/0.99  --smt_preprocessing                     true
% 3.14/0.99  --smt_ac_axioms                         fast
% 3.14/0.99  --preprocessed_out                      false
% 3.14/0.99  --preprocessed_stats                    false
% 3.14/0.99  
% 3.14/0.99  ------ Abstraction refinement Options
% 3.14/0.99  
% 3.14/0.99  --abstr_ref                             []
% 3.14/0.99  --abstr_ref_prep                        false
% 3.14/0.99  --abstr_ref_until_sat                   false
% 3.14/0.99  --abstr_ref_sig_restrict                funpre
% 3.14/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/0.99  --abstr_ref_under                       []
% 3.14/0.99  
% 3.14/0.99  ------ SAT Options
% 3.14/0.99  
% 3.14/0.99  --sat_mode                              false
% 3.14/0.99  --sat_fm_restart_options                ""
% 3.14/0.99  --sat_gr_def                            false
% 3.14/0.99  --sat_epr_types                         true
% 3.14/0.99  --sat_non_cyclic_types                  false
% 3.14/0.99  --sat_finite_models                     false
% 3.14/0.99  --sat_fm_lemmas                         false
% 3.14/0.99  --sat_fm_prep                           false
% 3.14/0.99  --sat_fm_uc_incr                        true
% 3.14/0.99  --sat_out_model                         small
% 3.14/0.99  --sat_out_clauses                       false
% 3.14/0.99  
% 3.14/0.99  ------ QBF Options
% 3.14/0.99  
% 3.14/0.99  --qbf_mode                              false
% 3.14/0.99  --qbf_elim_univ                         false
% 3.14/0.99  --qbf_dom_inst                          none
% 3.14/0.99  --qbf_dom_pre_inst                      false
% 3.14/0.99  --qbf_sk_in                             false
% 3.14/0.99  --qbf_pred_elim                         true
% 3.14/0.99  --qbf_split                             512
% 3.14/0.99  
% 3.14/0.99  ------ BMC1 Options
% 3.14/0.99  
% 3.14/0.99  --bmc1_incremental                      false
% 3.14/0.99  --bmc1_axioms                           reachable_all
% 3.14/0.99  --bmc1_min_bound                        0
% 3.14/0.99  --bmc1_max_bound                        -1
% 3.14/0.99  --bmc1_max_bound_default                -1
% 3.14/0.99  --bmc1_symbol_reachability              true
% 3.14/0.99  --bmc1_property_lemmas                  false
% 3.14/0.99  --bmc1_k_induction                      false
% 3.14/0.99  --bmc1_non_equiv_states                 false
% 3.14/0.99  --bmc1_deadlock                         false
% 3.14/0.99  --bmc1_ucm                              false
% 3.14/0.99  --bmc1_add_unsat_core                   none
% 3.14/0.99  --bmc1_unsat_core_children              false
% 3.14/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/0.99  --bmc1_out_stat                         full
% 3.14/0.99  --bmc1_ground_init                      false
% 3.14/0.99  --bmc1_pre_inst_next_state              false
% 3.14/0.99  --bmc1_pre_inst_state                   false
% 3.14/0.99  --bmc1_pre_inst_reach_state             false
% 3.14/0.99  --bmc1_out_unsat_core                   false
% 3.14/0.99  --bmc1_aig_witness_out                  false
% 3.14/0.99  --bmc1_verbose                          false
% 3.14/0.99  --bmc1_dump_clauses_tptp                false
% 3.14/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.14/0.99  --bmc1_dump_file                        -
% 3.14/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.14/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.14/0.99  --bmc1_ucm_extend_mode                  1
% 3.14/0.99  --bmc1_ucm_init_mode                    2
% 3.14/0.99  --bmc1_ucm_cone_mode                    none
% 3.14/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.14/0.99  --bmc1_ucm_relax_model                  4
% 3.14/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.14/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/0.99  --bmc1_ucm_layered_model                none
% 3.14/0.99  --bmc1_ucm_max_lemma_size               10
% 3.14/0.99  
% 3.14/0.99  ------ AIG Options
% 3.14/0.99  
% 3.14/0.99  --aig_mode                              false
% 3.14/0.99  
% 3.14/0.99  ------ Instantiation Options
% 3.14/0.99  
% 3.14/0.99  --instantiation_flag                    true
% 3.14/0.99  --inst_sos_flag                         false
% 3.14/0.99  --inst_sos_phase                        true
% 3.14/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/0.99  --inst_lit_sel_side                     num_symb
% 3.14/0.99  --inst_solver_per_active                1400
% 3.14/0.99  --inst_solver_calls_frac                1.
% 3.14/0.99  --inst_passive_queue_type               priority_queues
% 3.14/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/0.99  --inst_passive_queues_freq              [25;2]
% 3.14/0.99  --inst_dismatching                      true
% 3.14/0.99  --inst_eager_unprocessed_to_passive     true
% 3.14/0.99  --inst_prop_sim_given                   true
% 3.14/0.99  --inst_prop_sim_new                     false
% 3.14/0.99  --inst_subs_new                         false
% 3.14/0.99  --inst_eq_res_simp                      false
% 3.14/0.99  --inst_subs_given                       false
% 3.14/0.99  --inst_orphan_elimination               true
% 3.14/0.99  --inst_learning_loop_flag               true
% 3.14/0.99  --inst_learning_start                   3000
% 3.14/0.99  --inst_learning_factor                  2
% 3.14/0.99  --inst_start_prop_sim_after_learn       3
% 3.14/0.99  --inst_sel_renew                        solver
% 3.14/0.99  --inst_lit_activity_flag                true
% 3.14/0.99  --inst_restr_to_given                   false
% 3.14/0.99  --inst_activity_threshold               500
% 3.14/0.99  --inst_out_proof                        true
% 3.14/0.99  
% 3.14/0.99  ------ Resolution Options
% 3.14/0.99  
% 3.14/0.99  --resolution_flag                       true
% 3.14/0.99  --res_lit_sel                           adaptive
% 3.14/0.99  --res_lit_sel_side                      none
% 3.14/0.99  --res_ordering                          kbo
% 3.14/0.99  --res_to_prop_solver                    active
% 3.14/0.99  --res_prop_simpl_new                    false
% 3.14/0.99  --res_prop_simpl_given                  true
% 3.14/0.99  --res_passive_queue_type                priority_queues
% 3.14/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/0.99  --res_passive_queues_freq               [15;5]
% 3.14/0.99  --res_forward_subs                      full
% 3.14/0.99  --res_backward_subs                     full
% 3.14/0.99  --res_forward_subs_resolution           true
% 3.14/0.99  --res_backward_subs_resolution          true
% 3.14/0.99  --res_orphan_elimination                true
% 3.14/0.99  --res_time_limit                        2.
% 3.14/0.99  --res_out_proof                         true
% 3.14/0.99  
% 3.14/0.99  ------ Superposition Options
% 3.14/0.99  
% 3.14/0.99  --superposition_flag                    true
% 3.14/0.99  --sup_passive_queue_type                priority_queues
% 3.14/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.14/0.99  --demod_completeness_check              fast
% 3.14/0.99  --demod_use_ground                      true
% 3.14/0.99  --sup_to_prop_solver                    passive
% 3.14/0.99  --sup_prop_simpl_new                    true
% 3.14/0.99  --sup_prop_simpl_given                  true
% 3.14/0.99  --sup_fun_splitting                     false
% 3.14/0.99  --sup_smt_interval                      50000
% 3.14/0.99  
% 3.14/0.99  ------ Superposition Simplification Setup
% 3.14/0.99  
% 3.14/0.99  --sup_indices_passive                   []
% 3.14/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_full_bw                           [BwDemod]
% 3.14/0.99  --sup_immed_triv                        [TrivRules]
% 3.14/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_immed_bw_main                     []
% 3.14/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.99  
% 3.14/0.99  ------ Combination Options
% 3.14/0.99  
% 3.14/0.99  --comb_res_mult                         3
% 3.14/0.99  --comb_sup_mult                         2
% 3.14/0.99  --comb_inst_mult                        10
% 3.14/0.99  
% 3.14/0.99  ------ Debug Options
% 3.14/0.99  
% 3.14/0.99  --dbg_backtrace                         false
% 3.14/0.99  --dbg_dump_prop_clauses                 false
% 3.14/0.99  --dbg_dump_prop_clauses_file            -
% 3.14/0.99  --dbg_out_stat                          false
% 3.14/0.99  ------ Parsing...
% 3.14/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.14/0.99  ------ Proving...
% 3.14/0.99  ------ Problem Properties 
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  clauses                                 43
% 3.14/0.99  conjectures                             25
% 3.14/0.99  EPR                                     15
% 3.14/0.99  Horn                                    32
% 3.14/0.99  unary                                   16
% 3.14/0.99  binary                                  17
% 3.14/0.99  lits                                    126
% 3.14/0.99  lits eq                                 3
% 3.14/0.99  fd_pure                                 0
% 3.14/0.99  fd_pseudo                               0
% 3.14/0.99  fd_cond                                 0
% 3.14/0.99  fd_pseudo_cond                          0
% 3.14/0.99  AC symbols                              0
% 3.14/0.99  
% 3.14/0.99  ------ Schedule dynamic 5 is on 
% 3.14/0.99  
% 3.14/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  ------ 
% 3.14/0.99  Current options:
% 3.14/0.99  ------ 
% 3.14/0.99  
% 3.14/0.99  ------ Input Options
% 3.14/0.99  
% 3.14/0.99  --out_options                           all
% 3.14/0.99  --tptp_safe_out                         true
% 3.14/0.99  --problem_path                          ""
% 3.14/0.99  --include_path                          ""
% 3.14/0.99  --clausifier                            res/vclausify_rel
% 3.14/0.99  --clausifier_options                    --mode clausify
% 3.14/0.99  --stdin                                 false
% 3.14/0.99  --stats_out                             all
% 3.14/0.99  
% 3.14/0.99  ------ General Options
% 3.14/0.99  
% 3.14/0.99  --fof                                   false
% 3.14/0.99  --time_out_real                         305.
% 3.14/0.99  --time_out_virtual                      -1.
% 3.14/0.99  --symbol_type_check                     false
% 3.14/0.99  --clausify_out                          false
% 3.14/0.99  --sig_cnt_out                           false
% 3.14/0.99  --trig_cnt_out                          false
% 3.14/0.99  --trig_cnt_out_tolerance                1.
% 3.14/0.99  --trig_cnt_out_sk_spl                   false
% 3.14/0.99  --abstr_cl_out                          false
% 3.14/0.99  
% 3.14/0.99  ------ Global Options
% 3.14/0.99  
% 3.14/0.99  --schedule                              default
% 3.14/0.99  --add_important_lit                     false
% 3.14/0.99  --prop_solver_per_cl                    1000
% 3.14/0.99  --min_unsat_core                        false
% 3.14/0.99  --soft_assumptions                      false
% 3.14/0.99  --soft_lemma_size                       3
% 3.14/0.99  --prop_impl_unit_size                   0
% 3.14/0.99  --prop_impl_unit                        []
% 3.14/0.99  --share_sel_clauses                     true
% 3.14/0.99  --reset_solvers                         false
% 3.14/0.99  --bc_imp_inh                            [conj_cone]
% 3.14/0.99  --conj_cone_tolerance                   3.
% 3.14/0.99  --extra_neg_conj                        none
% 3.14/0.99  --large_theory_mode                     true
% 3.14/0.99  --prolific_symb_bound                   200
% 3.14/0.99  --lt_threshold                          2000
% 3.14/0.99  --clause_weak_htbl                      true
% 3.14/0.99  --gc_record_bc_elim                     false
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing Options
% 3.14/0.99  
% 3.14/0.99  --preprocessing_flag                    true
% 3.14/0.99  --time_out_prep_mult                    0.1
% 3.14/0.99  --splitting_mode                        input
% 3.14/0.99  --splitting_grd                         true
% 3.14/0.99  --splitting_cvd                         false
% 3.14/0.99  --splitting_cvd_svl                     false
% 3.14/0.99  --splitting_nvd                         32
% 3.14/0.99  --sub_typing                            true
% 3.14/0.99  --prep_gs_sim                           true
% 3.14/0.99  --prep_unflatten                        true
% 3.14/0.99  --prep_res_sim                          true
% 3.14/0.99  --prep_upred                            true
% 3.14/0.99  --prep_sem_filter                       exhaustive
% 3.14/0.99  --prep_sem_filter_out                   false
% 3.14/0.99  --pred_elim                             true
% 3.14/0.99  --res_sim_input                         true
% 3.14/0.99  --eq_ax_congr_red                       true
% 3.14/0.99  --pure_diseq_elim                       true
% 3.14/0.99  --brand_transform                       false
% 3.14/0.99  --non_eq_to_eq                          false
% 3.14/0.99  --prep_def_merge                        true
% 3.14/0.99  --prep_def_merge_prop_impl              false
% 3.14/0.99  --prep_def_merge_mbd                    true
% 3.14/0.99  --prep_def_merge_tr_red                 false
% 3.14/0.99  --prep_def_merge_tr_cl                  false
% 3.14/0.99  --smt_preprocessing                     true
% 3.14/0.99  --smt_ac_axioms                         fast
% 3.14/0.99  --preprocessed_out                      false
% 3.14/0.99  --preprocessed_stats                    false
% 3.14/0.99  
% 3.14/0.99  ------ Abstraction refinement Options
% 3.14/0.99  
% 3.14/0.99  --abstr_ref                             []
% 3.14/0.99  --abstr_ref_prep                        false
% 3.14/0.99  --abstr_ref_until_sat                   false
% 3.14/0.99  --abstr_ref_sig_restrict                funpre
% 3.14/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/0.99  --abstr_ref_under                       []
% 3.14/0.99  
% 3.14/0.99  ------ SAT Options
% 3.14/0.99  
% 3.14/0.99  --sat_mode                              false
% 3.14/0.99  --sat_fm_restart_options                ""
% 3.14/0.99  --sat_gr_def                            false
% 3.14/0.99  --sat_epr_types                         true
% 3.14/0.99  --sat_non_cyclic_types                  false
% 3.14/0.99  --sat_finite_models                     false
% 3.14/0.99  --sat_fm_lemmas                         false
% 3.14/0.99  --sat_fm_prep                           false
% 3.14/0.99  --sat_fm_uc_incr                        true
% 3.14/0.99  --sat_out_model                         small
% 3.14/0.99  --sat_out_clauses                       false
% 3.14/0.99  
% 3.14/0.99  ------ QBF Options
% 3.14/0.99  
% 3.14/0.99  --qbf_mode                              false
% 3.14/0.99  --qbf_elim_univ                         false
% 3.14/0.99  --qbf_dom_inst                          none
% 3.14/0.99  --qbf_dom_pre_inst                      false
% 3.14/0.99  --qbf_sk_in                             false
% 3.14/0.99  --qbf_pred_elim                         true
% 3.14/0.99  --qbf_split                             512
% 3.14/0.99  
% 3.14/0.99  ------ BMC1 Options
% 3.14/0.99  
% 3.14/0.99  --bmc1_incremental                      false
% 3.14/0.99  --bmc1_axioms                           reachable_all
% 3.14/0.99  --bmc1_min_bound                        0
% 3.14/0.99  --bmc1_max_bound                        -1
% 3.14/0.99  --bmc1_max_bound_default                -1
% 3.14/0.99  --bmc1_symbol_reachability              true
% 3.14/0.99  --bmc1_property_lemmas                  false
% 3.14/0.99  --bmc1_k_induction                      false
% 3.14/0.99  --bmc1_non_equiv_states                 false
% 3.14/0.99  --bmc1_deadlock                         false
% 3.14/0.99  --bmc1_ucm                              false
% 3.14/0.99  --bmc1_add_unsat_core                   none
% 3.14/0.99  --bmc1_unsat_core_children              false
% 3.14/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/0.99  --bmc1_out_stat                         full
% 3.14/0.99  --bmc1_ground_init                      false
% 3.14/0.99  --bmc1_pre_inst_next_state              false
% 3.14/0.99  --bmc1_pre_inst_state                   false
% 3.14/0.99  --bmc1_pre_inst_reach_state             false
% 3.14/0.99  --bmc1_out_unsat_core                   false
% 3.14/0.99  --bmc1_aig_witness_out                  false
% 3.14/0.99  --bmc1_verbose                          false
% 3.14/0.99  --bmc1_dump_clauses_tptp                false
% 3.14/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.14/0.99  --bmc1_dump_file                        -
% 3.14/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.14/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.14/0.99  --bmc1_ucm_extend_mode                  1
% 3.14/0.99  --bmc1_ucm_init_mode                    2
% 3.14/0.99  --bmc1_ucm_cone_mode                    none
% 3.14/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.14/0.99  --bmc1_ucm_relax_model                  4
% 3.14/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.14/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/0.99  --bmc1_ucm_layered_model                none
% 3.14/0.99  --bmc1_ucm_max_lemma_size               10
% 3.14/0.99  
% 3.14/0.99  ------ AIG Options
% 3.14/0.99  
% 3.14/0.99  --aig_mode                              false
% 3.14/0.99  
% 3.14/0.99  ------ Instantiation Options
% 3.14/0.99  
% 3.14/0.99  --instantiation_flag                    true
% 3.14/0.99  --inst_sos_flag                         false
% 3.14/0.99  --inst_sos_phase                        true
% 3.14/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/0.99  --inst_lit_sel_side                     none
% 3.14/0.99  --inst_solver_per_active                1400
% 3.14/0.99  --inst_solver_calls_frac                1.
% 3.14/0.99  --inst_passive_queue_type               priority_queues
% 3.14/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/0.99  --inst_passive_queues_freq              [25;2]
% 3.14/0.99  --inst_dismatching                      true
% 3.14/0.99  --inst_eager_unprocessed_to_passive     true
% 3.14/0.99  --inst_prop_sim_given                   true
% 3.14/0.99  --inst_prop_sim_new                     false
% 3.14/0.99  --inst_subs_new                         false
% 3.14/0.99  --inst_eq_res_simp                      false
% 3.14/0.99  --inst_subs_given                       false
% 3.14/0.99  --inst_orphan_elimination               true
% 3.14/0.99  --inst_learning_loop_flag               true
% 3.14/0.99  --inst_learning_start                   3000
% 3.14/0.99  --inst_learning_factor                  2
% 3.14/0.99  --inst_start_prop_sim_after_learn       3
% 3.14/0.99  --inst_sel_renew                        solver
% 3.14/0.99  --inst_lit_activity_flag                true
% 3.14/0.99  --inst_restr_to_given                   false
% 3.14/0.99  --inst_activity_threshold               500
% 3.14/0.99  --inst_out_proof                        true
% 3.14/0.99  
% 3.14/0.99  ------ Resolution Options
% 3.14/0.99  
% 3.14/0.99  --resolution_flag                       false
% 3.14/0.99  --res_lit_sel                           adaptive
% 3.14/0.99  --res_lit_sel_side                      none
% 3.14/0.99  --res_ordering                          kbo
% 3.14/0.99  --res_to_prop_solver                    active
% 3.14/0.99  --res_prop_simpl_new                    false
% 3.14/0.99  --res_prop_simpl_given                  true
% 3.14/0.99  --res_passive_queue_type                priority_queues
% 3.14/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/0.99  --res_passive_queues_freq               [15;5]
% 3.14/0.99  --res_forward_subs                      full
% 3.14/0.99  --res_backward_subs                     full
% 3.14/0.99  --res_forward_subs_resolution           true
% 3.14/0.99  --res_backward_subs_resolution          true
% 3.14/0.99  --res_orphan_elimination                true
% 3.14/0.99  --res_time_limit                        2.
% 3.14/0.99  --res_out_proof                         true
% 3.14/0.99  
% 3.14/0.99  ------ Superposition Options
% 3.14/0.99  
% 3.14/0.99  --superposition_flag                    true
% 3.14/0.99  --sup_passive_queue_type                priority_queues
% 3.14/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.14/0.99  --demod_completeness_check              fast
% 3.14/0.99  --demod_use_ground                      true
% 3.14/0.99  --sup_to_prop_solver                    passive
% 3.14/0.99  --sup_prop_simpl_new                    true
% 3.14/0.99  --sup_prop_simpl_given                  true
% 3.14/0.99  --sup_fun_splitting                     false
% 3.14/0.99  --sup_smt_interval                      50000
% 3.14/0.99  
% 3.14/0.99  ------ Superposition Simplification Setup
% 3.14/0.99  
% 3.14/0.99  --sup_indices_passive                   []
% 3.14/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_full_bw                           [BwDemod]
% 3.14/0.99  --sup_immed_triv                        [TrivRules]
% 3.14/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_immed_bw_main                     []
% 3.14/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.99  
% 3.14/0.99  ------ Combination Options
% 3.14/0.99  
% 3.14/0.99  --comb_res_mult                         3
% 3.14/0.99  --comb_sup_mult                         2
% 3.14/0.99  --comb_inst_mult                        10
% 3.14/0.99  
% 3.14/0.99  ------ Debug Options
% 3.14/0.99  
% 3.14/0.99  --dbg_backtrace                         false
% 3.14/0.99  --dbg_dump_prop_clauses                 false
% 3.14/0.99  --dbg_dump_prop_clauses_file            -
% 3.14/0.99  --dbg_out_stat                          false
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  ------ Proving...
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  % SZS status Theorem for theBenchmark.p
% 3.14/0.99  
% 3.14/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.14/0.99  
% 3.14/0.99  fof(f6,conjecture,(
% 3.14/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f7,negated_conjecture,(
% 3.14/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 3.14/0.99    inference(negated_conjecture,[],[f6])).
% 3.14/0.99  
% 3.14/0.99  fof(f17,plain,(
% 3.14/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & k1_tsep_1(X0,X3,X4) = X0) & (m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.14/0.99    inference(ennf_transformation,[],[f7])).
% 3.14/0.99  
% 3.14/0.99  fof(f18,plain,(
% 3.14/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.14/0.99    inference(flattening,[],[f17])).
% 3.14/0.99  
% 3.14/0.99  fof(f28,plain,(
% 3.14/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.14/0.99    inference(nnf_transformation,[],[f18])).
% 3.14/0.99  
% 3.14/0.99  fof(f29,plain,(
% 3.14/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.14/0.99    inference(flattening,[],[f28])).
% 3.14/0.99  
% 3.14/0.99  fof(f34,plain,(
% 3.14/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) => ((~m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & k1_tsep_1(X0,X3,sK6) = X0 & m1_pre_topc(sK6,X0) & v1_tsep_1(sK6,X0) & ~v2_struct_0(sK6))) )),
% 3.14/0.99    introduced(choice_axiom,[])).
% 3.14/0.99  
% 3.14/0.99  fof(f33,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK5)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK5))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & k1_tsep_1(X0,sK5,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK5,X0) & v1_tsep_1(sK5,X0) & ~v2_struct_0(sK5))) )),
% 3.14/0.99    introduced(choice_axiom,[])).
% 3.14/0.99  
% 3.14/0.99  fof(f32,plain,(
% 3.14/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(sK4,X0,X1) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) & m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X3))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK4,X0,X1) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.14/0.99    introduced(choice_axiom,[])).
% 3.14/0.99  
% 3.14/0.99  fof(f31,plain,(
% 3.14/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(X2,X0,sK3) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) & m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v5_pre_topc(X2,X0,sK3) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 3.14/0.99    introduced(choice_axiom,[])).
% 3.14/0.99  
% 3.14/0.99  fof(f30,plain,(
% 3.14/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2))) & k1_tsep_1(sK2,X3,X4) = sK2 & m1_pre_topc(X4,sK2) & v1_tsep_1(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & v1_tsep_1(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.14/0.99    introduced(choice_axiom,[])).
% 3.14/0.99  
% 3.14/0.99  fof(f35,plain,(
% 3.14/0.99    (((((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & k1_tsep_1(sK2,sK5,sK6) = sK2 & m1_pre_topc(sK6,sK2) & v1_tsep_1(sK6,sK2) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK2) & v1_tsep_1(sK5,sK2) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.14/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f29,f34,f33,f32,f31,f30])).
% 3.14/0.99  
% 3.14/0.99  fof(f69,plain,(
% 3.14/0.99    m1_pre_topc(sK6,sK2)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f63,plain,(
% 3.14/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f2,axiom,(
% 3.14/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f10,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.14/0.99    inference(ennf_transformation,[],[f2])).
% 3.14/0.99  
% 3.14/0.99  fof(f11,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.14/0.99    inference(flattening,[],[f10])).
% 3.14/0.99  
% 3.14/0.99  fof(f37,plain,(
% 3.14/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f11])).
% 3.14/0.99  
% 3.14/0.99  fof(f58,plain,(
% 3.14/0.99    ~v2_struct_0(sK3)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f59,plain,(
% 3.14/0.99    v2_pre_topc(sK3)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f60,plain,(
% 3.14/0.99    l1_pre_topc(sK3)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f61,plain,(
% 3.14/0.99    v1_funct_1(sK4)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f62,plain,(
% 3.14/0.99    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f1,axiom,(
% 3.14/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f8,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.14/0.99    inference(ennf_transformation,[],[f1])).
% 3.14/0.99  
% 3.14/0.99  fof(f9,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.14/0.99    inference(flattening,[],[f8])).
% 3.14/0.99  
% 3.14/0.99  fof(f36,plain,(
% 3.14/0.99    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f9])).
% 3.14/0.99  
% 3.14/0.99  fof(f55,plain,(
% 3.14/0.99    ~v2_struct_0(sK2)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f56,plain,(
% 3.14/0.99    v2_pre_topc(sK2)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f57,plain,(
% 3.14/0.99    l1_pre_topc(sK2)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f4,axiom,(
% 3.14/0.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f14,plain,(
% 3.14/0.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.14/0.99    inference(ennf_transformation,[],[f4])).
% 3.14/0.99  
% 3.14/0.99  fof(f53,plain,(
% 3.14/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f14])).
% 3.14/0.99  
% 3.14/0.99  fof(f70,plain,(
% 3.14/0.99    k1_tsep_1(sK2,sK5,sK6) = sK2),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f19,plain,(
% 3.14/0.99    ! [X1,X3,X4,X2,X0] : (sP0(X1,X3,X4,X2,X0) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))),
% 3.14/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.14/0.99  
% 3.14/0.99  fof(f25,plain,(
% 3.14/0.99    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 3.14/0.99    inference(nnf_transformation,[],[f19])).
% 3.14/0.99  
% 3.14/0.99  fof(f26,plain,(
% 3.14/0.99    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 3.14/0.99    inference(flattening,[],[f25])).
% 3.14/0.99  
% 3.14/0.99  fof(f27,plain,(
% 3.14/0.99    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) & ((m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) | ~sP0(X0,X1,X2,X3,X4)))),
% 3.14/0.99    inference(rectify,[],[f26])).
% 3.14/0.99  
% 3.14/0.99  fof(f51,plain,(
% 3.14/0.99    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) )),
% 3.14/0.99    inference(cnf_transformation,[],[f27])).
% 3.14/0.99  
% 3.14/0.99  fof(f66,plain,(
% 3.14/0.99    m1_pre_topc(sK5,sK2)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f20,plain,(
% 3.14/0.99    ! [X0,X2,X4,X3,X1] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> sP0(X1,X3,X4,X2,X0)) | ~sP1(X0,X2,X4,X3,X1))),
% 3.14/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.14/0.99  
% 3.14/0.99  fof(f22,plain,(
% 3.14/0.99    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)))) | ~sP1(X0,X2,X4,X3,X1))),
% 3.14/0.99    inference(nnf_transformation,[],[f20])).
% 3.14/0.99  
% 3.14/0.99  fof(f23,plain,(
% 3.14/0.99    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~sP1(X0,X2,X4,X3,X1))),
% 3.14/0.99    inference(flattening,[],[f22])).
% 3.14/0.99  
% 3.14/0.99  fof(f24,plain,(
% 3.14/0.99    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) & v1_funct_1(X2)) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) | ~v1_funct_1(X2))) | ~sP1(X0,X1,X2,X3,X4))),
% 3.14/0.99    inference(rectify,[],[f23])).
% 3.14/0.99  
% 3.14/0.99  fof(f38,plain,(
% 3.14/0.99    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) | ~v1_funct_1(X2) | ~sP1(X0,X1,X2,X3,X4)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f24])).
% 3.14/0.99  
% 3.14/0.99  fof(f103,plain,(
% 3.14/0.99    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f45,plain,(
% 3.14/0.99    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f27])).
% 3.14/0.99  
% 3.14/0.99  fof(f43,plain,(
% 3.14/0.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f27])).
% 3.14/0.99  
% 3.14/0.99  fof(f44,plain,(
% 3.14/0.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f27])).
% 3.14/0.99  
% 3.14/0.99  fof(f48,plain,(
% 3.14/0.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f27])).
% 3.14/0.99  
% 3.14/0.99  fof(f49,plain,(
% 3.14/0.99    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f27])).
% 3.14/0.99  
% 3.14/0.99  fof(f47,plain,(
% 3.14/0.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f27])).
% 3.14/0.99  
% 3.14/0.99  fof(f50,plain,(
% 3.14/0.99    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f27])).
% 3.14/0.99  
% 3.14/0.99  fof(f46,plain,(
% 3.14/0.99    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f27])).
% 3.14/0.99  
% 3.14/0.99  fof(f41,plain,(
% 3.14/0.99    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f24])).
% 3.14/0.99  
% 3.14/0.99  fof(f3,axiom,(
% 3.14/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))))))))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f12,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.14/0.99    inference(ennf_transformation,[],[f3])).
% 3.14/0.99  
% 3.14/0.99  fof(f13,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.14/0.99    inference(flattening,[],[f12])).
% 3.14/0.99  
% 3.14/0.99  fof(f21,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.14/0.99    inference(definition_folding,[],[f13,f20,f19])).
% 3.14/0.99  
% 3.14/0.99  fof(f52,plain,(
% 3.14/0.99    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f21])).
% 3.14/0.99  
% 3.14/0.99  fof(f5,axiom,(
% 3.14/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) => r4_tsep_1(X0,X1,X2))))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f15,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | (~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.14/0.99    inference(ennf_transformation,[],[f5])).
% 3.14/0.99  
% 3.14/0.99  fof(f16,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.14/0.99    inference(flattening,[],[f15])).
% 3.14/0.99  
% 3.14/0.99  fof(f54,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f16])).
% 3.14/0.99  
% 3.14/0.99  fof(f101,plain,(
% 3.14/0.99    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f97,plain,(
% 3.14/0.99    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f93,plain,(
% 3.14/0.99    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f89,plain,(
% 3.14/0.99    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | v5_pre_topc(sK4,sK2,sK3)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f85,plain,(
% 3.14/0.99    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f81,plain,(
% 3.14/0.99    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f77,plain,(
% 3.14/0.99    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f73,plain,(
% 3.14/0.99    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | v5_pre_topc(sK4,sK2,sK3)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f68,plain,(
% 3.14/0.99    v1_tsep_1(sK6,sK2)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f67,plain,(
% 3.14/0.99    ~v2_struct_0(sK6)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f65,plain,(
% 3.14/0.99    v1_tsep_1(sK5,sK2)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f64,plain,(
% 3.14/0.99    ~v2_struct_0(sK5)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2140,plain,
% 3.14/0.99      ( ~ m1_subset_1(X0_53,X0_55)
% 3.14/0.99      | m1_subset_1(X1_53,X1_55)
% 3.14/0.99      | X1_55 != X0_55
% 3.14/0.99      | X1_53 != X0_53 ),
% 3.14/0.99      theory(equality) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3721,plain,
% 3.14/0.99      ( m1_subset_1(X0_53,X0_55)
% 3.14/0.99      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.14/0.99      | X0_55 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
% 3.14/0.99      | X0_53 != X1_53 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_2140]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_7591,plain,
% 3.14/0.99      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
% 3.14/0.99      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.14/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
% 3.14/0.99      | X0_53 != X1_53 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_3721]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_7594,plain,
% 3.14/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
% 3.14/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.14/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
% 3.14/0.99      | sK4 != sK4 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_7591]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_53,negated_conjecture,
% 3.14/0.99      ( m1_pre_topc(sK6,sK2) ),
% 3.14/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2099,negated_conjecture,
% 3.14/0.99      ( m1_pre_topc(sK6,sK2) ),
% 3.14/0.99      inference(subtyping,[status(esa)],[c_53]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2960,plain,
% 3.14/0.99      ( m1_pre_topc(sK6,sK2) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2099]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_59,negated_conjecture,
% 3.14/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 3.14/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2093,negated_conjecture,
% 3.14/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 3.14/0.99      inference(subtyping,[status(esa)],[c_59]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2966,plain,
% 3.14/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2093]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1,plain,
% 3.14/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.14/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.14/0.99      | ~ m1_pre_topc(X3,X4)
% 3.14/0.99      | ~ m1_pre_topc(X3,X1)
% 3.14/0.99      | ~ m1_pre_topc(X1,X4)
% 3.14/0.99      | v2_struct_0(X4)
% 3.14/0.99      | v2_struct_0(X2)
% 3.14/0.99      | ~ v2_pre_topc(X2)
% 3.14/0.99      | ~ v2_pre_topc(X4)
% 3.14/0.99      | ~ l1_pre_topc(X2)
% 3.14/0.99      | ~ l1_pre_topc(X4)
% 3.14/0.99      | ~ v1_funct_1(X0)
% 3.14/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2124,plain,
% 3.14/0.99      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 3.14/0.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 3.14/0.99      | ~ m1_pre_topc(X2_52,X0_52)
% 3.14/0.99      | ~ m1_pre_topc(X2_52,X3_52)
% 3.14/0.99      | ~ m1_pre_topc(X0_52,X3_52)
% 3.14/0.99      | v2_struct_0(X1_52)
% 3.14/0.99      | v2_struct_0(X3_52)
% 3.14/0.99      | ~ v2_pre_topc(X3_52)
% 3.14/0.99      | ~ v2_pre_topc(X1_52)
% 3.14/0.99      | ~ l1_pre_topc(X3_52)
% 3.14/0.99      | ~ l1_pre_topc(X1_52)
% 3.14/0.99      | ~ v1_funct_1(X0_53)
% 3.14/0.99      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53) ),
% 3.14/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2936,plain,
% 3.14/0.99      ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53)
% 3.14/0.99      | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 3.14/0.99      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 3.14/0.99      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 3.14/0.99      | m1_pre_topc(X2_52,X3_52) != iProver_top
% 3.14/0.99      | m1_pre_topc(X0_52,X3_52) != iProver_top
% 3.14/0.99      | v2_struct_0(X1_52) = iProver_top
% 3.14/0.99      | v2_struct_0(X3_52) = iProver_top
% 3.14/0.99      | v2_pre_topc(X1_52) != iProver_top
% 3.14/0.99      | v2_pre_topc(X3_52) != iProver_top
% 3.14/0.99      | l1_pre_topc(X1_52) != iProver_top
% 3.14/0.99      | l1_pre_topc(X3_52) != iProver_top
% 3.14/0.99      | v1_funct_1(X0_53) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2124]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3795,plain,
% 3.14/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK3,sK2,X0_52,sK4)
% 3.14/0.99      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 3.14/0.99      | m1_pre_topc(X0_52,sK2) != iProver_top
% 3.14/0.99      | m1_pre_topc(sK2,X1_52) != iProver_top
% 3.14/0.99      | v2_struct_0(X1_52) = iProver_top
% 3.14/0.99      | v2_struct_0(sK3) = iProver_top
% 3.14/0.99      | v2_pre_topc(X1_52) != iProver_top
% 3.14/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.14/0.99      | l1_pre_topc(X1_52) != iProver_top
% 3.14/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.14/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2966,c_2936]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_64,negated_conjecture,
% 3.14/0.99      ( ~ v2_struct_0(sK3) ),
% 3.14/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_71,plain,
% 3.14/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_64]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_63,negated_conjecture,
% 3.14/0.99      ( v2_pre_topc(sK3) ),
% 3.14/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_72,plain,
% 3.14/0.99      ( v2_pre_topc(sK3) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_63]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_62,negated_conjecture,
% 3.14/0.99      ( l1_pre_topc(sK3) ),
% 3.14/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_73,plain,
% 3.14/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_61,negated_conjecture,
% 3.14/0.99      ( v1_funct_1(sK4) ),
% 3.14/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_74,plain,
% 3.14/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_60,negated_conjecture,
% 3.14/0.99      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 3.14/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_75,plain,
% 3.14/0.99      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4116,plain,
% 3.14/0.99      ( v2_pre_topc(X1_52) != iProver_top
% 3.14/0.99      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK3,sK2,X0_52,sK4)
% 3.14/0.99      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 3.14/0.99      | m1_pre_topc(X0_52,sK2) != iProver_top
% 3.14/0.99      | m1_pre_topc(sK2,X1_52) != iProver_top
% 3.14/0.99      | v2_struct_0(X1_52) = iProver_top
% 3.14/0.99      | l1_pre_topc(X1_52) != iProver_top ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_3795,c_71,c_72,c_73,c_74,c_75]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4117,plain,
% 3.14/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK3,sK2,X0_52,sK4)
% 3.14/0.99      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 3.14/0.99      | m1_pre_topc(X0_52,sK2) != iProver_top
% 3.14/0.99      | m1_pre_topc(sK2,X1_52) != iProver_top
% 3.14/0.99      | v2_struct_0(X1_52) = iProver_top
% 3.14/0.99      | v2_pre_topc(X1_52) != iProver_top
% 3.14/0.99      | l1_pre_topc(X1_52) != iProver_top ),
% 3.14/0.99      inference(renaming,[status(thm)],[c_4116]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4129,plain,
% 3.14/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK6)) = k3_tmap_1(sK2,sK3,sK2,sK6,sK4)
% 3.14/0.99      | m1_pre_topc(sK6,sK2) != iProver_top
% 3.14/0.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.14/0.99      | v2_struct_0(sK2) = iProver_top
% 3.14/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.14/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2960,c_4117]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_0,plain,
% 3.14/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.14/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.14/0.99      | ~ m1_pre_topc(X3,X1)
% 3.14/0.99      | v2_struct_0(X1)
% 3.14/0.99      | v2_struct_0(X2)
% 3.14/0.99      | ~ v2_pre_topc(X2)
% 3.14/0.99      | ~ v2_pre_topc(X1)
% 3.14/0.99      | ~ l1_pre_topc(X2)
% 3.14/0.99      | ~ l1_pre_topc(X1)
% 3.14/0.99      | ~ v1_funct_1(X0)
% 3.14/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.14/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2125,plain,
% 3.14/0.99      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 3.14/0.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 3.14/0.99      | ~ m1_pre_topc(X2_52,X0_52)
% 3.14/0.99      | v2_struct_0(X0_52)
% 3.14/0.99      | v2_struct_0(X1_52)
% 3.14/0.99      | ~ v2_pre_topc(X0_52)
% 3.14/0.99      | ~ v2_pre_topc(X1_52)
% 3.14/0.99      | ~ l1_pre_topc(X0_52)
% 3.14/0.99      | ~ l1_pre_topc(X1_52)
% 3.14/0.99      | ~ v1_funct_1(X0_53)
% 3.14/0.99      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_53,X2_52) ),
% 3.14/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2935,plain,
% 3.14/0.99      ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_53,X2_52)
% 3.14/0.99      | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 3.14/0.99      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 3.14/0.99      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 3.14/0.99      | v2_struct_0(X0_52) = iProver_top
% 3.14/0.99      | v2_struct_0(X1_52) = iProver_top
% 3.14/0.99      | v2_pre_topc(X0_52) != iProver_top
% 3.14/0.99      | v2_pre_topc(X1_52) != iProver_top
% 3.14/0.99      | l1_pre_topc(X0_52) != iProver_top
% 3.14/0.99      | l1_pre_topc(X1_52) != iProver_top
% 3.14/0.99      | v1_funct_1(X0_53) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2125]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3633,plain,
% 3.14/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK2,sK3,sK4,X0_52)
% 3.14/0.99      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | m1_pre_topc(X0_52,sK2) != iProver_top
% 3.14/0.99      | v2_struct_0(sK3) = iProver_top
% 3.14/0.99      | v2_struct_0(sK2) = iProver_top
% 3.14/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.14/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.14/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.14/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.14/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2966,c_2935]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_67,negated_conjecture,
% 3.14/0.99      ( ~ v2_struct_0(sK2) ),
% 3.14/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_68,plain,
% 3.14/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_67]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_66,negated_conjecture,
% 3.14/0.99      ( v2_pre_topc(sK2) ),
% 3.14/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_69,plain,
% 3.14/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_66]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_65,negated_conjecture,
% 3.14/0.99      ( l1_pre_topc(sK2) ),
% 3.14/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_70,plain,
% 3.14/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_65]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4023,plain,
% 3.14/0.99      ( m1_pre_topc(X0_52,sK2) != iProver_top
% 3.14/0.99      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK2,sK3,sK4,X0_52) ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_3633,c_68,c_69,c_70,c_71,c_72,c_73,c_74,c_75]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4024,plain,
% 3.14/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK2,sK3,sK4,X0_52)
% 3.14/0.99      | m1_pre_topc(X0_52,sK2) != iProver_top ),
% 3.14/0.99      inference(renaming,[status(thm)],[c_4023]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4031,plain,
% 3.14/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK6)) = k2_tmap_1(sK2,sK3,sK4,sK6) ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2960,c_4024]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4163,plain,
% 3.14/0.99      ( k3_tmap_1(sK2,sK3,sK2,sK6,sK4) = k2_tmap_1(sK2,sK3,sK4,sK6)
% 3.14/0.99      | m1_pre_topc(sK6,sK2) != iProver_top
% 3.14/0.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.14/0.99      | v2_struct_0(sK2) = iProver_top
% 3.14/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.14/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.14/0.99      inference(light_normalisation,[status(thm)],[c_4129,c_4031]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_82,plain,
% 3.14/0.99      ( m1_pre_topc(sK6,sK2) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_17,plain,
% 3.14/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2109,plain,
% 3.14/0.99      ( m1_pre_topc(X0_52,X0_52) | ~ l1_pre_topc(X0_52) ),
% 3.14/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3436,plain,
% 3.14/0.99      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_2109]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3439,plain,
% 3.14/0.99      ( m1_pre_topc(sK2,sK2) = iProver_top
% 3.14/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_3436]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5858,plain,
% 3.14/0.99      ( k3_tmap_1(sK2,sK3,sK2,sK6,sK4) = k2_tmap_1(sK2,sK3,sK4,sK6) ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_4163,c_68,c_69,c_70,c_82,c_3439]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_52,negated_conjecture,
% 3.14/0.99      ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
% 3.14/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2100,negated_conjecture,
% 3.14/0.99      ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
% 3.14/0.99      inference(subtyping,[status(esa)],[c_52]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_7,plain,
% 3.14/0.99      ( sP0(X0,X1,X2,X3,X4)
% 3.14/0.99      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
% 3.14/0.99      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
% 3.14/0.99      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
% 3.14/0.99      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
% 3.14/0.99      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 3.14/0.99      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
% 3.14/0.99      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
% 3.14/0.99      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
% 3.14/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2118,plain,
% 3.14/0.99      ( sP0(X0_52,X1_52,X0_53,X2_52,X3_52)
% 3.14/0.99      | ~ v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),X1_52,X0_52)
% 3.14/0.99      | ~ v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),X2_52,X0_52)
% 3.14/0.99      | ~ v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),u1_struct_0(X1_52),u1_struct_0(X0_52))
% 3.14/0.99      | ~ v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),u1_struct_0(X2_52),u1_struct_0(X0_52))
% 3.14/0.99      | ~ m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52))))
% 3.14/0.99      | ~ m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X0_52))))
% 3.14/0.99      | ~ v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53))
% 3.14/0.99      | ~ v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53)) ),
% 3.14/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2942,plain,
% 3.14/0.99      ( sP0(X0_52,X1_52,X0_53,X2_52,X3_52) = iProver_top
% 3.14/0.99      | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),X1_52,X0_52) != iProver_top
% 3.14/0.99      | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),X2_52,X0_52) != iProver_top
% 3.14/0.99      | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 3.14/0.99      | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),u1_struct_0(X2_52),u1_struct_0(X0_52)) != iProver_top
% 3.14/0.99      | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 3.14/0.99      | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X0_52)))) != iProver_top
% 3.14/0.99      | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53)) != iProver_top
% 3.14/0.99      | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53)) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2118]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_7106,plain,
% 3.14/0.99      ( sP0(X0_52,sK6,X0_53,sK5,sK2) = iProver_top
% 3.14/0.99      | v5_pre_topc(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK5,X0_53),sK5,X0_52) != iProver_top
% 3.14/0.99      | v5_pre_topc(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK6,X0_53),sK6,X0_52) != iProver_top
% 3.14/0.99      | v1_funct_2(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_52)) != iProver_top
% 3.14/0.99      | v1_funct_2(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK6,X0_53),u1_struct_0(sK6),u1_struct_0(X0_52)) != iProver_top
% 3.14/0.99      | m1_subset_1(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_52)))) != iProver_top
% 3.14/0.99      | m1_subset_1(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_52)))) != iProver_top
% 3.14/0.99      | v1_funct_1(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK5,X0_53)) != iProver_top
% 3.14/0.99      | v1_funct_1(k3_tmap_1(sK2,X0_52,k1_tsep_1(sK2,sK5,sK6),sK6,X0_53)) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2100,c_2942]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_7116,plain,
% 3.14/0.99      ( sP0(X0_52,sK6,X0_53,sK5,sK2) = iProver_top
% 3.14/0.99      | v5_pre_topc(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_53),sK5,X0_52) != iProver_top
% 3.14/0.99      | v5_pre_topc(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_53),sK6,X0_52) != iProver_top
% 3.14/0.99      | v1_funct_2(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_52)) != iProver_top
% 3.14/0.99      | v1_funct_2(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_53),u1_struct_0(sK6),u1_struct_0(X0_52)) != iProver_top
% 3.14/0.99      | m1_subset_1(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_52)))) != iProver_top
% 3.14/0.99      | m1_subset_1(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_52)))) != iProver_top
% 3.14/0.99      | v1_funct_1(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_53)) != iProver_top
% 3.14/0.99      | v1_funct_1(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_53)) != iProver_top ),
% 3.14/0.99      inference(light_normalisation,[status(thm)],[c_7106,c_2100]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_7186,plain,
% 3.14/0.99      ( sP0(sK3,sK6,sK4,sK5,sK2) = iProver_top
% 3.14/0.99      | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,sK4),sK5,sK3) != iProver_top
% 3.14/0.99      | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK6,sK4),sK6,sK3) != iProver_top
% 3.14/0.99      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,sK4),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK6,sK4),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.14/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 3.14/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,sK4)) != iProver_top
% 3.14/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK6,sK4)) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_5858,c_7116]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_56,negated_conjecture,
% 3.14/0.99      ( m1_pre_topc(sK5,sK2) ),
% 3.14/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2096,negated_conjecture,
% 3.14/0.99      ( m1_pre_topc(sK5,sK2) ),
% 3.14/0.99      inference(subtyping,[status(esa)],[c_56]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2963,plain,
% 3.14/0.99      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2096]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4130,plain,
% 3.14/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK5)) = k3_tmap_1(sK2,sK3,sK2,sK5,sK4)
% 3.14/0.99      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.14/0.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.14/0.99      | v2_struct_0(sK2) = iProver_top
% 3.14/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.14/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2963,c_4117]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4032,plain,
% 3.14/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK5)) = k2_tmap_1(sK2,sK3,sK4,sK5) ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2963,c_4024]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4150,plain,
% 3.14/0.99      ( k3_tmap_1(sK2,sK3,sK2,sK5,sK4) = k2_tmap_1(sK2,sK3,sK4,sK5)
% 3.14/0.99      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.14/0.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.14/0.99      | v2_struct_0(sK2) = iProver_top
% 3.14/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.14/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.14/0.99      inference(light_normalisation,[status(thm)],[c_4130,c_4032]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_79,plain,
% 3.14/0.99      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5408,plain,
% 3.14/0.99      ( k3_tmap_1(sK2,sK3,sK2,sK5,sK4) = k2_tmap_1(sK2,sK3,sK4,sK5) ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_4150,c_68,c_69,c_70,c_79,c_3439]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_7196,plain,
% 3.14/0.99      ( sP0(sK3,sK6,sK4,sK5,sK2) = iProver_top
% 3.14/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 3.14/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 3.14/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.14/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 3.14/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 3.14/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 3.14/0.99      inference(light_normalisation,[status(thm)],[c_7186,c_5408,c_5858]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_7206,plain,
% 3.14/0.99      ( sP0(sK3,sK6,sK4,sK5,sK2)
% 3.14/0.99      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 3.14/0.99      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 3.14/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.14/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 3.14/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.14/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 3.14/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 3.14/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 3.14/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_7196]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6,plain,
% 3.14/0.99      ( ~ sP1(X0,X1,X2,X3,X4)
% 3.14/0.99      | sP0(X4,X3,X2,X1,X0)
% 3.14/0.99      | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
% 3.14/0.99      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 3.14/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 3.14/0.99      | ~ v1_funct_1(X2) ),
% 3.14/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2119,plain,
% 3.14/0.99      ( ~ sP1(X0_52,X1_52,X0_53,X2_52,X3_52)
% 3.14/0.99      | sP0(X3_52,X2_52,X0_53,X1_52,X0_52)
% 3.14/0.99      | ~ v5_pre_topc(X0_53,k1_tsep_1(X0_52,X1_52,X2_52),X3_52)
% 3.14/0.99      | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))
% 3.14/0.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))))
% 3.14/0.99      | ~ v1_funct_1(X0_53) ),
% 3.14/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2941,plain,
% 3.14/0.99      ( sP1(X0_52,X1_52,X0_53,X2_52,X3_52) != iProver_top
% 3.14/0.99      | sP0(X3_52,X2_52,X0_53,X1_52,X0_52) = iProver_top
% 3.14/0.99      | v5_pre_topc(X0_53,k1_tsep_1(X0_52,X1_52,X2_52),X3_52) != iProver_top
% 3.14/0.99      | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52)) != iProver_top
% 3.14/0.99      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52)))) != iProver_top
% 3.14/0.99      | v1_funct_1(X0_53) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2119]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6072,plain,
% 3.14/0.99      ( sP1(sK2,sK5,X0_53,sK6,X0_52) != iProver_top
% 3.14/0.99      | sP0(X0_52,sK6,X0_53,sK5,sK2) = iProver_top
% 3.14/0.99      | v5_pre_topc(X0_53,k1_tsep_1(sK2,sK5,sK6),X0_52) != iProver_top
% 3.14/0.99      | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_52)) != iProver_top
% 3.14/0.99      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 3.14/0.99      | v1_funct_1(X0_53) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2100,c_2941]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6079,plain,
% 3.14/0.99      ( sP1(sK2,sK5,X0_53,sK6,X0_52) != iProver_top
% 3.14/0.99      | sP0(X0_52,sK6,X0_53,sK5,sK2) = iProver_top
% 3.14/0.99      | v5_pre_topc(X0_53,sK2,X0_52) != iProver_top
% 3.14/0.99      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 3.14/0.99      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 3.14/0.99      | v1_funct_1(X0_53) != iProver_top ),
% 3.14/0.99      inference(light_normalisation,[status(thm)],[c_6072,c_2100]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6604,plain,
% 3.14/0.99      ( sP1(sK2,sK5,sK4,sK6,sK3) != iProver_top
% 3.14/0.99      | sP0(sK3,sK6,sK4,sK5,sK2) = iProver_top
% 3.14/0.99      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 3.14/0.99      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2966,c_6079]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_19,negated_conjecture,
% 3.14/0.99      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 3.14/0.99      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 3.14/0.99      | ~ v5_pre_topc(sK4,sK2,sK3)
% 3.14/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.14/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 3.14/0.99      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.14/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.14/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 3.14/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.14/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 3.14/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 3.14/0.99      | ~ v1_funct_1(sK4) ),
% 3.14/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_443,plain,
% 3.14/0.99      ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 3.14/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 3.14/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 3.14/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.14/0.99      | ~ v5_pre_topc(sK4,sK2,sK3)
% 3.14/0.99      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 3.14/0.99      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 3.14/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.14/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_19,c_61,c_60,c_59]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_444,negated_conjecture,
% 3.14/0.99      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 3.14/0.99      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 3.14/0.99      | ~ v5_pre_topc(sK4,sK2,sK3)
% 3.14/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.14/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 3.14/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.14/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 3.14/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 3.14/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 3.14/0.99      inference(renaming,[status(thm)],[c_443]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_445,plain,
% 3.14/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 3.14/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 3.14/0.99      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 3.14/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.14/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 3.14/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 3.14/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_444]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_13,plain,
% 3.14/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.14/0.99      | v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2112,plain,
% 3.14/0.99      ( ~ sP0(X0_52,X1_52,X0_53,X2_52,X3_52)
% 3.14/0.99      | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),X2_52,X0_52) ),
% 3.14/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2948,plain,
% 3.14/0.99      ( sP0(X0_52,X1_52,X0_53,X2_52,X3_52) != iProver_top
% 3.14/0.99      | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),X2_52,X0_52) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2112]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5154,plain,
% 3.14/0.99      ( sP0(X0_52,sK6,X0_53,sK5,sK2) != iProver_top
% 3.14/0.99      | v5_pre_topc(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_53),sK5,X0_52) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2100,c_2948]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5411,plain,
% 3.14/0.99      ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
% 3.14/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_5408,c_5154]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_15,plain,
% 3.14/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.14/0.99      | v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
% 3.14/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2110,plain,
% 3.14/0.99      ( ~ sP0(X0_52,X1_52,X0_53,X2_52,X3_52)
% 3.14/0.99      | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53)) ),
% 3.14/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2950,plain,
% 3.14/0.99      ( sP0(X0_52,X1_52,X0_53,X2_52,X3_52) != iProver_top
% 3.14/0.99      | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53)) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2110]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4486,plain,
% 3.14/0.99      ( sP0(X0_52,sK6,X0_53,sK5,sK2) != iProver_top
% 3.14/0.99      | v1_funct_1(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_53)) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2100,c_2950]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5412,plain,
% 3.14/0.99      ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
% 3.14/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_5408,c_4486]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_14,plain,
% 3.14/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.14/0.99      | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) ),
% 3.14/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2111,plain,
% 3.14/0.99      ( ~ sP0(X0_52,X1_52,X0_53,X2_52,X3_52)
% 3.14/0.99      | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),u1_struct_0(X2_52),u1_struct_0(X0_52)) ),
% 3.14/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2949,plain,
% 3.14/0.99      ( sP0(X0_52,X1_52,X0_53,X2_52,X3_52) != iProver_top
% 3.14/0.99      | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),u1_struct_0(X2_52),u1_struct_0(X0_52)) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2111]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5604,plain,
% 3.14/0.99      ( sP0(X0_52,sK6,X0_53,sK5,sK2) != iProver_top
% 3.14/0.99      | v1_funct_2(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_52)) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2100,c_2949]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5714,plain,
% 3.14/0.99      ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
% 3.14/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_5408,c_5604]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_10,plain,
% 3.14/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.14/0.99      | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) ),
% 3.14/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2115,plain,
% 3.14/0.99      ( ~ sP0(X0_52,X1_52,X0_53,X2_52,X3_52)
% 3.14/0.99      | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),u1_struct_0(X1_52),u1_struct_0(X0_52)) ),
% 3.14/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2945,plain,
% 3.14/0.99      ( sP0(X0_52,X1_52,X0_53,X2_52,X3_52) != iProver_top
% 3.14/0.99      | v1_funct_2(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),u1_struct_0(X1_52),u1_struct_0(X0_52)) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2115]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5509,plain,
% 3.14/0.99      ( sP0(X0_52,sK6,X0_53,sK5,sK2) != iProver_top
% 3.14/0.99      | v1_funct_2(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_53),u1_struct_0(sK6),u1_struct_0(X0_52)) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2100,c_2945]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5861,plain,
% 3.14/0.99      ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
% 3.14/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_5858,c_5509]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_9,plain,
% 3.14/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.14/0.99      | v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2116,plain,
% 3.14/0.99      ( ~ sP0(X0_52,X1_52,X0_53,X2_52,X3_52)
% 3.14/0.99      | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),X1_52,X0_52) ),
% 3.14/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2944,plain,
% 3.14/0.99      ( sP0(X0_52,X1_52,X0_53,X2_52,X3_52) != iProver_top
% 3.14/0.99      | v5_pre_topc(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),X1_52,X0_52) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2116]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5104,plain,
% 3.14/0.99      ( sP0(X0_52,sK6,X0_53,sK5,sK2) != iProver_top
% 3.14/0.99      | v5_pre_topc(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_53),sK6,X0_52) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2100,c_2944]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5862,plain,
% 3.14/0.99      ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
% 3.14/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_5858,c_5104]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_11,plain,
% 3.14/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.14/0.99      | v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) ),
% 3.14/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2114,plain,
% 3.14/0.99      ( ~ sP0(X0_52,X1_52,X0_53,X2_52,X3_52)
% 3.14/0.99      | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53)) ),
% 3.14/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2946,plain,
% 3.14/0.99      ( sP0(X0_52,X1_52,X0_53,X2_52,X3_52) != iProver_top
% 3.14/0.99      | v1_funct_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53)) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2114]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4430,plain,
% 3.14/0.99      ( sP0(X0_52,sK6,X0_53,sK5,sK2) != iProver_top
% 3.14/0.99      | v1_funct_1(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_53)) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2100,c_2946]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5863,plain,
% 3.14/0.99      ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
% 3.14/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_5858,c_4430]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_8,plain,
% 3.14/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.14/0.99      | m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
% 3.14/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2117,plain,
% 3.14/0.99      ( ~ sP0(X0_52,X1_52,X0_53,X2_52,X3_52)
% 3.14/0.99      | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) ),
% 3.14/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2943,plain,
% 3.14/0.99      ( sP0(X0_52,X1_52,X0_53,X2_52,X3_52) != iProver_top
% 3.14/0.99      | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X1_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2117]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6147,plain,
% 3.14/0.99      ( sP0(X0_52,sK6,X0_53,sK5,sK2) != iProver_top
% 3.14/0.99      | m1_subset_1(k3_tmap_1(sK2,X0_52,sK2,sK6,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_52)))) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2100,c_2943]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6230,plain,
% 3.14/0.99      ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
% 3.14/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_5858,c_6147]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_12,plain,
% 3.14/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.14/0.99      | m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ),
% 3.14/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2113,plain,
% 3.14/0.99      ( ~ sP0(X0_52,X1_52,X0_53,X2_52,X3_52)
% 3.14/0.99      | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X0_52)))) ),
% 3.14/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2947,plain,
% 3.14/0.99      ( sP0(X0_52,X1_52,X0_53,X2_52,X3_52) != iProver_top
% 3.14/0.99      | m1_subset_1(k3_tmap_1(X3_52,X0_52,k1_tsep_1(X3_52,X2_52,X1_52),X2_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X0_52)))) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2113]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6341,plain,
% 3.14/0.99      ( sP0(X0_52,sK6,X0_53,sK5,sK2) != iProver_top
% 3.14/0.99      | m1_subset_1(k3_tmap_1(sK2,X0_52,sK2,sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_52)))) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2100,c_2947]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6420,plain,
% 3.14/0.99      ( sP0(sK3,sK6,sK4,sK5,sK2) != iProver_top
% 3.14/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_5408,c_6341]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6878,plain,
% 3.14/0.99      ( sP1(sK2,sK5,sK4,sK6,sK3) != iProver_top
% 3.14/0.99      | v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_6604,c_74,c_75,c_445,c_5411,c_5412,c_5714,c_5861,
% 3.14/0.99                 c_5862,c_5863,c_6230,c_6420]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6880,plain,
% 3.14/0.99      ( ~ sP1(sK2,sK5,sK4,sK6,sK3) | ~ v5_pre_topc(sK4,sK2,sK3) ),
% 3.14/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6878]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2139,plain,
% 3.14/0.99      ( X0_56 != X1_56 | k1_zfmisc_1(X0_56) = k1_zfmisc_1(X1_56) ),
% 3.14/0.99      theory(equality) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3451,plain,
% 3.14/0.99      ( X0_56 != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))
% 3.14/0.99      | k1_zfmisc_1(X0_56) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_2139]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3725,plain,
% 3.14/0.99      ( k2_zfmisc_1(X0_54,X1_54) != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))
% 3.14/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_3451]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5609,plain,
% 3.14/0.99      ( k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))
% 3.14/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_3725]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2138,plain,
% 3.14/0.99      ( k2_zfmisc_1(X0_54,X1_54) = k2_zfmisc_1(X2_54,X3_54)
% 3.14/0.99      | X0_54 != X2_54
% 3.14/0.99      | X1_54 != X3_54 ),
% 3.14/0.99      theory(equality) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3726,plain,
% 3.14/0.99      ( k2_zfmisc_1(X0_54,X1_54) = k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))
% 3.14/0.99      | X1_54 != u1_struct_0(sK3)
% 3.14/0.99      | X0_54 != u1_struct_0(sK2) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_2138]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4316,plain,
% 3.14/0.99      ( k2_zfmisc_1(X0_54,u1_struct_0(sK3)) = k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))
% 3.14/0.99      | X0_54 != u1_struct_0(sK2)
% 3.14/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_3726]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5123,plain,
% 3.14/0.99      ( k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) = k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))
% 3.14/0.99      | u1_struct_0(k1_tsep_1(sK2,sK5,sK6)) != u1_struct_0(sK2)
% 3.14/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_4316]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3,plain,
% 3.14/0.99      ( ~ sP1(X0,X1,X2,X3,X4)
% 3.14/0.99      | ~ sP0(X4,X3,X2,X1,X0)
% 3.14/0.99      | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
% 3.14/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2122,plain,
% 3.14/0.99      ( ~ sP1(X0_52,X1_52,X0_53,X2_52,X3_52)
% 3.14/0.99      | ~ sP0(X3_52,X2_52,X0_53,X1_52,X0_52)
% 3.14/0.99      | v5_pre_topc(X0_53,k1_tsep_1(X0_52,X1_52,X2_52),X3_52) ),
% 3.14/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2938,plain,
% 3.14/0.99      ( sP1(X0_52,X1_52,X0_53,X2_52,X3_52) != iProver_top
% 3.14/0.99      | sP0(X3_52,X2_52,X0_53,X1_52,X0_52) != iProver_top
% 3.14/0.99      | v5_pre_topc(X0_53,k1_tsep_1(X0_52,X1_52,X2_52),X3_52) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2122]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5050,plain,
% 3.14/0.99      ( sP1(sK2,sK5,X0_53,sK6,X0_52) != iProver_top
% 3.14/0.99      | sP0(X0_52,sK6,X0_53,sK5,sK2) != iProver_top
% 3.14/0.99      | v5_pre_topc(X0_53,sK2,X0_52) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2100,c_2938]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5051,plain,
% 3.14/0.99      ( ~ sP1(sK2,sK5,X0_53,sK6,X0_52)
% 3.14/0.99      | ~ sP0(X0_52,sK6,X0_53,sK5,sK2)
% 3.14/0.99      | v5_pre_topc(X0_53,sK2,X0_52) ),
% 3.14/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5050]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5053,plain,
% 3.14/0.99      ( ~ sP1(sK2,sK5,sK4,sK6,sK3)
% 3.14/0.99      | ~ sP0(sK3,sK6,sK4,sK5,sK2)
% 3.14/0.99      | v5_pre_topc(sK4,sK2,sK3) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_5051]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2141,plain,
% 3.14/0.99      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 3.14/0.99      | v1_funct_2(X1_53,X2_54,X3_54)
% 3.14/0.99      | X2_54 != X0_54
% 3.14/0.99      | X3_54 != X1_54
% 3.14/0.99      | X1_53 != X0_53 ),
% 3.14/0.99      theory(equality) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3362,plain,
% 3.14/0.99      ( v1_funct_2(X0_53,X0_54,X1_54)
% 3.14/0.99      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.14/0.99      | X1_54 != u1_struct_0(sK3)
% 3.14/0.99      | X0_54 != u1_struct_0(sK2)
% 3.14/0.99      | X0_53 != sK4 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_2141]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3483,plain,
% 3.14/0.99      ( v1_funct_2(X0_53,X0_54,u1_struct_0(X0_52))
% 3.14/0.99      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.14/0.99      | X0_54 != u1_struct_0(sK2)
% 3.14/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK3)
% 3.14/0.99      | X0_53 != sK4 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_3362]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4502,plain,
% 3.14/0.99      ( v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_52))
% 3.14/0.99      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.14/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK3)
% 3.14/0.99      | u1_struct_0(k1_tsep_1(sK2,sK5,sK6)) != u1_struct_0(sK2)
% 3.14/0.99      | X0_53 != sK4 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_3483]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4505,plain,
% 3.14/0.99      ( v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
% 3.14/0.99      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.14/0.99      | u1_struct_0(k1_tsep_1(sK2,sK5,sK6)) != u1_struct_0(sK2)
% 3.14/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.14/0.99      | sK4 != sK4 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_4502]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2135,plain,
% 3.14/0.99      ( u1_struct_0(X0_52) = u1_struct_0(X1_52) | X0_52 != X1_52 ),
% 3.14/0.99      theory(equality) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3839,plain,
% 3.14/0.99      ( u1_struct_0(X0_52) = u1_struct_0(sK2) | X0_52 != sK2 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_2135]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4306,plain,
% 3.14/0.99      ( u1_struct_0(k1_tsep_1(sK2,sK5,sK6)) = u1_struct_0(sK2)
% 3.14/0.99      | k1_tsep_1(sK2,sK5,sK6) != sK2 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_3839]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_16,plain,
% 3.14/0.99      ( sP1(X0,X1,X2,X3,X4)
% 3.14/0.99      | ~ r4_tsep_1(X0,X1,X3)
% 3.14/0.99      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 3.14/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 3.14/0.99      | ~ m1_pre_topc(X3,X0)
% 3.14/0.99      | ~ m1_pre_topc(X1,X0)
% 3.14/0.99      | v2_struct_0(X0)
% 3.14/0.99      | v2_struct_0(X4)
% 3.14/0.99      | v2_struct_0(X1)
% 3.14/0.99      | v2_struct_0(X3)
% 3.14/0.99      | ~ v2_pre_topc(X4)
% 3.14/0.99      | ~ v2_pre_topc(X0)
% 3.14/0.99      | ~ l1_pre_topc(X4)
% 3.14/0.99      | ~ l1_pre_topc(X0)
% 3.14/0.99      | ~ v1_funct_1(X2) ),
% 3.14/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_18,plain,
% 3.14/0.99      ( r4_tsep_1(X0,X1,X2)
% 3.14/0.99      | ~ v1_tsep_1(X2,X0)
% 3.14/0.99      | ~ v1_tsep_1(X1,X0)
% 3.14/0.99      | ~ m1_pre_topc(X2,X0)
% 3.14/0.99      | ~ m1_pre_topc(X1,X0)
% 3.14/0.99      | v2_struct_0(X0)
% 3.14/0.99      | ~ v2_pre_topc(X0)
% 3.14/0.99      | ~ l1_pre_topc(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_674,plain,
% 3.14/0.99      ( sP1(X0,X1,X2,X3,X4)
% 3.14/0.99      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 3.14/0.99      | ~ v1_tsep_1(X5,X6)
% 3.14/0.99      | ~ v1_tsep_1(X7,X6)
% 3.14/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 3.14/0.99      | ~ m1_pre_topc(X3,X0)
% 3.14/0.99      | ~ m1_pre_topc(X1,X0)
% 3.14/0.99      | ~ m1_pre_topc(X5,X6)
% 3.14/0.99      | ~ m1_pre_topc(X7,X6)
% 3.14/0.99      | v2_struct_0(X0)
% 3.14/0.99      | v2_struct_0(X1)
% 3.14/0.99      | v2_struct_0(X4)
% 3.14/0.99      | v2_struct_0(X3)
% 3.14/0.99      | v2_struct_0(X6)
% 3.14/0.99      | ~ v2_pre_topc(X0)
% 3.14/0.99      | ~ v2_pre_topc(X4)
% 3.14/0.99      | ~ v2_pre_topc(X6)
% 3.14/0.99      | ~ l1_pre_topc(X0)
% 3.14/0.99      | ~ l1_pre_topc(X4)
% 3.14/0.99      | ~ l1_pre_topc(X6)
% 3.14/0.99      | ~ v1_funct_1(X2)
% 3.14/0.99      | X5 != X3
% 3.14/0.99      | X7 != X1
% 3.14/0.99      | X6 != X0 ),
% 3.14/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_675,plain,
% 3.14/0.99      ( sP1(X0,X1,X2,X3,X4)
% 3.14/0.99      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 3.14/0.99      | ~ v1_tsep_1(X1,X0)
% 3.14/0.99      | ~ v1_tsep_1(X3,X0)
% 3.14/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 3.14/0.99      | ~ m1_pre_topc(X3,X0)
% 3.14/0.99      | ~ m1_pre_topc(X1,X0)
% 3.14/0.99      | v2_struct_0(X0)
% 3.14/0.99      | v2_struct_0(X1)
% 3.14/0.99      | v2_struct_0(X4)
% 3.14/0.99      | v2_struct_0(X3)
% 3.14/0.99      | ~ v2_pre_topc(X0)
% 3.14/0.99      | ~ v2_pre_topc(X4)
% 3.14/0.99      | ~ l1_pre_topc(X0)
% 3.14/0.99      | ~ l1_pre_topc(X4)
% 3.14/0.99      | ~ v1_funct_1(X2) ),
% 3.14/0.99      inference(unflattening,[status(thm)],[c_674]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2083,plain,
% 3.14/0.99      ( sP1(X0_52,X1_52,X0_53,X2_52,X3_52)
% 3.14/0.99      | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))
% 3.14/0.99      | ~ v1_tsep_1(X1_52,X0_52)
% 3.14/0.99      | ~ v1_tsep_1(X2_52,X0_52)
% 3.14/0.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))))
% 3.14/0.99      | ~ m1_pre_topc(X1_52,X0_52)
% 3.14/0.99      | ~ m1_pre_topc(X2_52,X0_52)
% 3.14/0.99      | v2_struct_0(X0_52)
% 3.14/0.99      | v2_struct_0(X1_52)
% 3.14/0.99      | v2_struct_0(X3_52)
% 3.14/0.99      | v2_struct_0(X2_52)
% 3.14/0.99      | ~ v2_pre_topc(X0_52)
% 3.14/0.99      | ~ v2_pre_topc(X3_52)
% 3.14/0.99      | ~ l1_pre_topc(X0_52)
% 3.14/0.99      | ~ l1_pre_topc(X3_52)
% 3.14/0.99      | ~ v1_funct_1(X0_53) ),
% 3.14/0.99      inference(subtyping,[status(esa)],[c_675]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3405,plain,
% 3.14/0.99      ( sP1(sK2,sK5,X0_53,X0_52,X1_52)
% 3.14/0.99      | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK5,X0_52)),u1_struct_0(X1_52))
% 3.14/0.99      | ~ v1_tsep_1(X0_52,sK2)
% 3.14/0.99      | ~ v1_tsep_1(sK5,sK2)
% 3.14/0.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,X0_52)),u1_struct_0(X1_52))))
% 3.14/0.99      | ~ m1_pre_topc(X0_52,sK2)
% 3.14/0.99      | ~ m1_pre_topc(sK5,sK2)
% 3.14/0.99      | v2_struct_0(X0_52)
% 3.14/0.99      | v2_struct_0(X1_52)
% 3.14/0.99      | v2_struct_0(sK5)
% 3.14/0.99      | v2_struct_0(sK2)
% 3.14/0.99      | ~ v2_pre_topc(X1_52)
% 3.14/0.99      | ~ v2_pre_topc(sK2)
% 3.14/0.99      | ~ l1_pre_topc(X1_52)
% 3.14/0.99      | ~ l1_pre_topc(sK2)
% 3.14/0.99      | ~ v1_funct_1(X0_53) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_2083]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3521,plain,
% 3.14/0.99      ( sP1(sK2,sK5,X0_53,sK6,X0_52)
% 3.14/0.99      | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_52))
% 3.14/0.99      | ~ v1_tsep_1(sK5,sK2)
% 3.14/0.99      | ~ v1_tsep_1(sK6,sK2)
% 3.14/0.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_52))))
% 3.14/0.99      | ~ m1_pre_topc(sK5,sK2)
% 3.14/0.99      | ~ m1_pre_topc(sK6,sK2)
% 3.14/0.99      | v2_struct_0(X0_52)
% 3.14/0.99      | v2_struct_0(sK5)
% 3.14/0.99      | v2_struct_0(sK6)
% 3.14/0.99      | v2_struct_0(sK2)
% 3.14/0.99      | ~ v2_pre_topc(X0_52)
% 3.14/0.99      | ~ v2_pre_topc(sK2)
% 3.14/0.99      | ~ l1_pre_topc(X0_52)
% 3.14/0.99      | ~ l1_pre_topc(sK2)
% 3.14/0.99      | ~ v1_funct_1(X0_53) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_3405]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3523,plain,
% 3.14/0.99      ( sP1(sK2,sK5,sK4,sK6,sK3)
% 3.14/0.99      | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
% 3.14/0.99      | ~ v1_tsep_1(sK5,sK2)
% 3.14/0.99      | ~ v1_tsep_1(sK6,sK2)
% 3.14/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
% 3.14/0.99      | ~ m1_pre_topc(sK5,sK2)
% 3.14/0.99      | ~ m1_pre_topc(sK6,sK2)
% 3.14/0.99      | v2_struct_0(sK5)
% 3.14/0.99      | v2_struct_0(sK6)
% 3.14/0.99      | v2_struct_0(sK3)
% 3.14/0.99      | v2_struct_0(sK2)
% 3.14/0.99      | ~ v2_pre_topc(sK3)
% 3.14/0.99      | ~ v2_pre_topc(sK2)
% 3.14/0.99      | ~ l1_pre_topc(sK3)
% 3.14/0.99      | ~ l1_pre_topc(sK2)
% 3.14/0.99      | ~ v1_funct_1(sK4) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_3521]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2128,plain,( X0_53 = X0_53 ),theory(equality) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2168,plain,
% 3.14/0.99      ( sK4 = sK4 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_2128]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2127,plain,( X0_52 = X0_52 ),theory(equality) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2167,plain,
% 3.14/0.99      ( sK3 = sK3 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_2127]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2151,plain,
% 3.14/0.99      ( u1_struct_0(sK3) = u1_struct_0(sK3) | sK3 != sK3 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_2135]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_21,negated_conjecture,
% 3.14/0.99      ( v5_pre_topc(sK4,sK2,sK3)
% 3.14/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 3.14/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_25,negated_conjecture,
% 3.14/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 3.14/0.99      | v5_pre_topc(sK4,sK2,sK3) ),
% 3.14/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_29,negated_conjecture,
% 3.14/0.99      ( v5_pre_topc(sK4,sK2,sK3)
% 3.14/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
% 3.14/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_33,negated_conjecture,
% 3.14/0.99      ( v5_pre_topc(sK4,sK2,sK3)
% 3.14/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 3.14/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_37,negated_conjecture,
% 3.14/0.99      ( v5_pre_topc(sK4,sK2,sK3)
% 3.14/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 3.14/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_41,negated_conjecture,
% 3.14/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 3.14/0.99      | v5_pre_topc(sK4,sK2,sK3) ),
% 3.14/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_45,negated_conjecture,
% 3.14/0.99      ( v5_pre_topc(sK4,sK2,sK3)
% 3.14/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 3.14/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_49,negated_conjecture,
% 3.14/0.99      ( v5_pre_topc(sK4,sK2,sK3)
% 3.14/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
% 3.14/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_54,negated_conjecture,
% 3.14/0.99      ( v1_tsep_1(sK6,sK2) ),
% 3.14/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_55,negated_conjecture,
% 3.14/0.99      ( ~ v2_struct_0(sK6) ),
% 3.14/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_57,negated_conjecture,
% 3.14/0.99      ( v1_tsep_1(sK5,sK2) ),
% 3.14/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_58,negated_conjecture,
% 3.14/0.99      ( ~ v2_struct_0(sK5) ),
% 3.14/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(contradiction,plain,
% 3.14/0.99      ( $false ),
% 3.14/0.99      inference(minisat,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_7594,c_7206,c_6880,c_5609,c_5123,c_5053,c_4505,c_4306,
% 3.14/0.99                 c_3523,c_2100,c_2168,c_2167,c_2151,c_21,c_25,c_29,c_33,
% 3.14/0.99                 c_37,c_41,c_45,c_49,c_53,c_54,c_55,c_56,c_57,c_58,c_59,
% 3.14/0.99                 c_60,c_61,c_62,c_63,c_64,c_65,c_66,c_67]) ).
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.14/0.99  
% 3.14/0.99  ------                               Statistics
% 3.14/0.99  
% 3.14/0.99  ------ General
% 3.14/0.99  
% 3.14/0.99  abstr_ref_over_cycles:                  0
% 3.14/0.99  abstr_ref_under_cycles:                 0
% 3.14/0.99  gc_basic_clause_elim:                   0
% 3.14/0.99  forced_gc_time:                         0
% 3.14/0.99  parsing_time:                           0.018
% 3.14/0.99  unif_index_cands_time:                  0.
% 3.14/0.99  unif_index_add_time:                    0.
% 3.14/0.99  orderings_time:                         0.
% 3.14/0.99  out_proof_time:                         0.024
% 3.14/0.99  total_time:                             0.291
% 3.14/0.99  num_of_symbols:                         57
% 3.14/0.99  num_of_terms:                           5412
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing
% 3.14/0.99  
% 3.14/0.99  num_of_splits:                          0
% 3.14/0.99  num_of_split_atoms:                     0
% 3.14/0.99  num_of_reused_defs:                     0
% 3.14/0.99  num_eq_ax_congr_red:                    48
% 3.14/0.99  num_of_sem_filtered_clauses:            1
% 3.14/0.99  num_of_subtypes:                        5
% 3.14/0.99  monotx_restored_types:                  0
% 3.14/0.99  sat_num_of_epr_types:                   0
% 3.14/0.99  sat_num_of_non_cyclic_types:            0
% 3.14/0.99  sat_guarded_non_collapsed_types:        0
% 3.14/0.99  num_pure_diseq_elim:                    0
% 3.14/0.99  simp_replaced_by:                       0
% 3.14/0.99  res_preprocessed:                       220
% 3.14/0.99  prep_upred:                             0
% 3.14/0.99  prep_unflattend:                        123
% 3.14/0.99  smt_new_axioms:                         0
% 3.14/0.99  pred_elim_cands:                        11
% 3.14/0.99  pred_elim:                              1
% 3.14/0.99  pred_elim_cl:                           1
% 3.14/0.99  pred_elim_cycles:                       5
% 3.14/0.99  merged_defs:                            0
% 3.14/0.99  merged_defs_ncl:                        0
% 3.14/0.99  bin_hyper_res:                          0
% 3.14/0.99  prep_cycles:                            4
% 3.14/0.99  pred_elim_time:                         0.028
% 3.14/0.99  splitting_time:                         0.
% 3.14/0.99  sem_filter_time:                        0.
% 3.14/0.99  monotx_time:                            0.
% 3.14/0.99  subtype_inf_time:                       0.001
% 3.14/0.99  
% 3.14/0.99  ------ Problem properties
% 3.14/0.99  
% 3.14/0.99  clauses:                                43
% 3.14/0.99  conjectures:                            25
% 3.14/0.99  epr:                                    15
% 3.14/0.99  horn:                                   32
% 3.14/0.99  ground:                                 25
% 3.14/0.99  unary:                                  16
% 3.14/0.99  binary:                                 17
% 3.14/0.99  lits:                                   126
% 3.14/0.99  lits_eq:                                3
% 3.14/0.99  fd_pure:                                0
% 3.14/0.99  fd_pseudo:                              0
% 3.14/0.99  fd_cond:                                0
% 3.14/0.99  fd_pseudo_cond:                         0
% 3.14/0.99  ac_symbols:                             0
% 3.14/0.99  
% 3.14/0.99  ------ Propositional Solver
% 3.14/0.99  
% 3.14/0.99  prop_solver_calls:                      29
% 3.14/0.99  prop_fast_solver_calls:                 2141
% 3.14/0.99  smt_solver_calls:                       0
% 3.14/0.99  smt_fast_solver_calls:                  0
% 3.14/0.99  prop_num_of_clauses:                    1935
% 3.14/0.99  prop_preprocess_simplified:             7778
% 3.14/0.99  prop_fo_subsumed:                       113
% 3.14/0.99  prop_solver_time:                       0.
% 3.14/0.99  smt_solver_time:                        0.
% 3.14/0.99  smt_fast_solver_time:                   0.
% 3.14/0.99  prop_fast_solver_time:                  0.
% 3.14/0.99  prop_unsat_core_time:                   0.
% 3.14/0.99  
% 3.14/0.99  ------ QBF
% 3.14/0.99  
% 3.14/0.99  qbf_q_res:                              0
% 3.14/0.99  qbf_num_tautologies:                    0
% 3.14/0.99  qbf_prep_cycles:                        0
% 3.14/0.99  
% 3.14/0.99  ------ BMC1
% 3.14/0.99  
% 3.14/0.99  bmc1_current_bound:                     -1
% 3.14/0.99  bmc1_last_solved_bound:                 -1
% 3.14/0.99  bmc1_unsat_core_size:                   -1
% 3.14/0.99  bmc1_unsat_core_parents_size:           -1
% 3.14/0.99  bmc1_merge_next_fun:                    0
% 3.14/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.14/0.99  
% 3.14/0.99  ------ Instantiation
% 3.14/0.99  
% 3.14/0.99  inst_num_of_clauses:                    644
% 3.14/0.99  inst_num_in_passive:                    131
% 3.14/0.99  inst_num_in_active:                     429
% 3.14/0.99  inst_num_in_unprocessed:                85
% 3.14/0.99  inst_num_of_loops:                      478
% 3.14/0.99  inst_num_of_learning_restarts:          0
% 3.14/0.99  inst_num_moves_active_passive:          41
% 3.14/0.99  inst_lit_activity:                      0
% 3.14/0.99  inst_lit_activity_moves:                0
% 3.14/0.99  inst_num_tautologies:                   0
% 3.14/0.99  inst_num_prop_implied:                  0
% 3.14/0.99  inst_num_existing_simplified:           0
% 3.14/0.99  inst_num_eq_res_simplified:             0
% 3.14/0.99  inst_num_child_elim:                    0
% 3.14/0.99  inst_num_of_dismatching_blockings:      127
% 3.14/0.99  inst_num_of_non_proper_insts:           646
% 3.14/0.99  inst_num_of_duplicates:                 0
% 3.14/0.99  inst_inst_num_from_inst_to_res:         0
% 3.14/0.99  inst_dismatching_checking_time:         0.
% 3.14/0.99  
% 3.14/0.99  ------ Resolution
% 3.14/0.99  
% 3.14/0.99  res_num_of_clauses:                     0
% 3.14/0.99  res_num_in_passive:                     0
% 3.14/0.99  res_num_in_active:                      0
% 3.14/0.99  res_num_of_loops:                       224
% 3.14/0.99  res_forward_subset_subsumed:            75
% 3.14/0.99  res_backward_subset_subsumed:           8
% 3.14/0.99  res_forward_subsumed:                   0
% 3.14/0.99  res_backward_subsumed:                  0
% 3.14/0.99  res_forward_subsumption_resolution:     0
% 3.14/0.99  res_backward_subsumption_resolution:    0
% 3.14/0.99  res_clause_to_clause_subsumption:       289
% 3.14/0.99  res_orphan_elimination:                 0
% 3.14/0.99  res_tautology_del:                      141
% 3.14/0.99  res_num_eq_res_simplified:              0
% 3.14/0.99  res_num_sel_changes:                    0
% 3.14/0.99  res_moves_from_active_to_pass:          0
% 3.14/0.99  
% 3.14/0.99  ------ Superposition
% 3.14/0.99  
% 3.14/0.99  sup_time_total:                         0.
% 3.14/0.99  sup_time_generating:                    0.
% 3.14/0.99  sup_time_sim_full:                      0.
% 3.14/0.99  sup_time_sim_immed:                     0.
% 3.14/0.99  
% 3.14/0.99  sup_num_of_clauses:                     116
% 3.14/0.99  sup_num_in_active:                      94
% 3.14/0.99  sup_num_in_passive:                     22
% 3.14/0.99  sup_num_of_loops:                       94
% 3.14/0.99  sup_fw_superposition:                   51
% 3.14/0.99  sup_bw_superposition:                   30
% 3.14/0.99  sup_immediate_simplified:               8
% 3.14/0.99  sup_given_eliminated:                   0
% 3.14/0.99  comparisons_done:                       0
% 3.14/0.99  comparisons_avoided:                    0
% 3.14/0.99  
% 3.14/0.99  ------ Simplifications
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  sim_fw_subset_subsumed:                 0
% 3.14/0.99  sim_bw_subset_subsumed:                 0
% 3.14/0.99  sim_fw_subsumed:                        0
% 3.14/0.99  sim_bw_subsumed:                        0
% 3.14/0.99  sim_fw_subsumption_res:                 12
% 3.14/0.99  sim_bw_subsumption_res:                 0
% 3.14/0.99  sim_tautology_del:                      8
% 3.14/0.99  sim_eq_tautology_del:                   0
% 3.14/0.99  sim_eq_res_simp:                        0
% 3.14/0.99  sim_fw_demodulated:                     0
% 3.14/0.99  sim_bw_demodulated:                     0
% 3.14/0.99  sim_light_normalised:                   8
% 3.14/0.99  sim_joinable_taut:                      0
% 3.14/0.99  sim_joinable_simp:                      0
% 3.14/0.99  sim_ac_normalised:                      0
% 3.14/0.99  sim_smt_subsumption:                    0
% 3.14/0.99  
%------------------------------------------------------------------------------
