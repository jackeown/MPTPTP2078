%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:20 EST 2020

% Result     : Theorem 7.43s
% Output     : CNFRefutation 7.43s
% Verified   : 
% Statistics : Number of formulae       :  316 (5111 expanded)
%              Number of clauses        :  223 (1117 expanded)
%              Number of leaves         :   21 (1785 expanded)
%              Depth                    :   24
%              Number of atoms          : 2286 (161838 expanded)
%              Number of equality atoms :  527 (6210 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal clause size      :   78 (   5 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

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
    inference(nnf_transformation,[],[f33])).

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
    inference(flattening,[],[f44])).

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f45,f50,f49,f48,f47,f46])).

fof(f127,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f95,plain,(
    k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f51])).

fof(f35,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
      <=> sP0(X1,X3,X4,X0,X2) )
      | ~ sP1(X2,X0,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

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
    inference(nnf_transformation,[],[f35])).

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
    inference(flattening,[],[f38])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f40])).

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
    inference(nnf_transformation,[],[f34])).

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
    inference(flattening,[],[f41])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f82,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f89,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f51])).

fof(f90,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f91,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f92,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f93,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f94,plain,(
    m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f96,plain,(
    r4_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f28])).

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
    inference(definition_folding,[],[f29,f35,f34])).

fof(f80,plain,(
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

fof(f115,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
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
    inference(cnf_transformation,[],[f27])).

fof(f99,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f123,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f107,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f119,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f103,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
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
    inference(pure_predicate_removal,[],[f6])).

fof(f22,plain,(
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

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f21])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f19])).

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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f43])).

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
    inference(cnf_transformation,[],[f51])).

cnf(c_32,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_878,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1870,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_878])).

cnf(c_64,negated_conjecture,
    ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_869,negated_conjecture,
    ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(subtyping,[status(esa)],[c_64])).

cnf(c_14,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_894,plain,
    ( ~ sP1(X0_54,X1_54,X0_53,X2_54,X3_54)
    | ~ sP0(X3_54,X2_54,X0_53,X1_54,X0_54)
    | m1_subset_1(k2_tmap_1(X1_54,X3_54,X0_53,k1_tsep_1(X1_54,X0_54,X2_54)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_54,X0_54,X2_54)),u1_struct_0(X3_54)))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1854,plain,
    ( sP1(X0_54,X1_54,X0_53,X2_54,X3_54) != iProver_top
    | sP0(X3_54,X2_54,X0_53,X1_54,X0_54) != iProver_top
    | m1_subset_1(k2_tmap_1(X1_54,X3_54,X0_53,k1_tsep_1(X1_54,X0_54,X2_54)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_54,X0_54,X2_54)),u1_struct_0(X3_54)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_894])).

cnf(c_7927,plain,
    ( sP1(sK5,sK2,X0_53,sK6,X0_54) != iProver_top
    | sP0(X0_54,sK6,X0_53,sK2,sK5) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_53,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_869,c_1854])).

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
    inference(cnf_transformation,[],[f79])).

cnf(c_889,plain,
    ( sP0(X0_54,X1_54,X0_53,X2_54,X3_54)
    | ~ v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_53,X1_54),X1_54,X0_54)
    | ~ v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_53,X3_54),X3_54,X0_54)
    | ~ v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_53,X1_54),u1_struct_0(X1_54),u1_struct_0(X0_54))
    | ~ v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_53,X3_54),u1_struct_0(X3_54),u1_struct_0(X0_54))
    | ~ m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_53,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54))))
    | ~ m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_53,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X0_54))))
    | ~ v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_53,X1_54))
    | ~ v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_53,X3_54)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1859,plain,
    ( sP0(X0_54,X1_54,X0_53,X2_54,X3_54) = iProver_top
    | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_53,X1_54),X1_54,X0_54) != iProver_top
    | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_53,X3_54),X3_54,X0_54) != iProver_top
    | v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_53,X1_54),u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_53,X3_54),u1_struct_0(X3_54),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_53,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_53,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_53,X1_54)) != iProver_top
    | v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_53,X3_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_889])).

cnf(c_11684,plain,
    ( sP1(sK5,sK2,X0_53,sK6,X0_54) != iProver_top
    | sP0(X0_54,sK6,X0_53,sK2,sK5) != iProver_top
    | sP0(X0_54,sK2,X0_53,sK2,X1_54) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_53,X1_54),X1_54,X0_54) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_53,sK2),sK2,X0_54) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_53,X1_54),u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_53,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_53,X1_54)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_53,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7927,c_1859])).

cnf(c_17,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_891,plain,
    ( ~ sP1(X0_54,X1_54,X0_53,X2_54,X3_54)
    | ~ sP0(X3_54,X2_54,X0_53,X1_54,X0_54)
    | v1_funct_1(k2_tmap_1(X1_54,X3_54,X0_53,k1_tsep_1(X1_54,X0_54,X2_54))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1857,plain,
    ( sP1(X0_54,X1_54,X0_53,X2_54,X3_54) != iProver_top
    | sP0(X3_54,X2_54,X0_53,X1_54,X0_54) != iProver_top
    | v1_funct_1(k2_tmap_1(X1_54,X3_54,X0_53,k1_tsep_1(X1_54,X0_54,X2_54))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_891])).

cnf(c_4856,plain,
    ( sP1(sK5,sK2,X0_53,sK6,X0_54) != iProver_top
    | sP0(X0_54,sK6,X0_53,sK2,sK5) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_53,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_869,c_1857])).

cnf(c_15,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_893,plain,
    ( ~ sP1(X0_54,X1_54,X0_53,X2_54,X3_54)
    | ~ sP0(X3_54,X2_54,X0_53,X1_54,X0_54)
    | v5_pre_topc(k2_tmap_1(X1_54,X3_54,X0_53,k1_tsep_1(X1_54,X0_54,X2_54)),k1_tsep_1(X1_54,X0_54,X2_54),X3_54) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1855,plain,
    ( sP1(X0_54,X1_54,X0_53,X2_54,X3_54) != iProver_top
    | sP0(X3_54,X2_54,X0_53,X1_54,X0_54) != iProver_top
    | v5_pre_topc(k2_tmap_1(X1_54,X3_54,X0_53,k1_tsep_1(X1_54,X0_54,X2_54)),k1_tsep_1(X1_54,X0_54,X2_54),X3_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_893])).

cnf(c_5841,plain,
    ( sP1(sK5,sK2,X0_53,sK6,X0_54) != iProver_top
    | sP0(X0_54,sK6,X0_53,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_53,sK2),sK2,X0_54) = iProver_top ),
    inference(superposition,[status(thm)],[c_869,c_1855])).

cnf(c_16,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_892,plain,
    ( ~ sP1(X0_54,X1_54,X0_53,X2_54,X3_54)
    | ~ sP0(X3_54,X2_54,X0_53,X1_54,X0_54)
    | v1_funct_2(k2_tmap_1(X1_54,X3_54,X0_53,k1_tsep_1(X1_54,X0_54,X2_54)),u1_struct_0(k1_tsep_1(X1_54,X0_54,X2_54)),u1_struct_0(X3_54)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1856,plain,
    ( sP1(X0_54,X1_54,X0_53,X2_54,X3_54) != iProver_top
    | sP0(X3_54,X2_54,X0_53,X1_54,X0_54) != iProver_top
    | v1_funct_2(k2_tmap_1(X1_54,X3_54,X0_53,k1_tsep_1(X1_54,X0_54,X2_54)),u1_struct_0(k1_tsep_1(X1_54,X0_54,X2_54)),u1_struct_0(X3_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_892])).

cnf(c_6007,plain,
    ( sP1(sK5,sK2,X0_53,sK6,X0_54) != iProver_top
    | sP0(X0_54,sK6,X0_53,sK2,sK5) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) = iProver_top ),
    inference(superposition,[status(thm)],[c_869,c_1856])).

cnf(c_13344,plain,
    ( v1_funct_1(k2_tmap_1(sK2,X0_54,X0_53,X1_54)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_53,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_53,X1_54),X1_54,X0_54) != iProver_top
    | sP0(X0_54,sK2,X0_53,sK2,X1_54) = iProver_top
    | sP0(X0_54,sK6,X0_53,sK2,sK5) != iProver_top
    | sP1(sK5,sK2,X0_53,sK6,X0_54) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_53,X1_54),u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11684,c_4856,c_5841,c_6007])).

cnf(c_13345,plain,
    ( sP1(sK5,sK2,X0_53,sK6,X0_54) != iProver_top
    | sP0(X0_54,sK6,X0_53,sK2,sK5) != iProver_top
    | sP0(X0_54,sK2,X0_53,sK2,X1_54) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_53,X1_54),X1_54,X0_54) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_53,X1_54),u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_53,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_53,X1_54)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13344])).

cnf(c_13357,plain,
    ( sP1(sK5,sK2,sK4,sK6,sK3) != iProver_top
    | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | sP0(sK3,sK2,sK4,sK2,sK6) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1870,c_13345])).

cnf(c_77,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_78,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_77])).

cnf(c_76,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_79,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_76])).

cnf(c_75,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_80,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_75])).

cnf(c_74,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_81,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_74])).

cnf(c_73,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_82,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_72,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_83,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_72])).

cnf(c_71,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_84,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_70,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_85,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_70])).

cnf(c_69,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_86,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_68,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_87,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_68])).

cnf(c_67,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_88,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_67])).

cnf(c_66,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_89,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66])).

cnf(c_65,negated_conjecture,
    ( m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_90,plain,
    ( m1_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65])).

cnf(c_63,negated_conjecture,
    ( r4_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_91,plain,
    ( r4_tsep_1(sK2,sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_196,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_198,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_196])).

cnf(c_28,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ r4_tsep_1(X1,X0,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_880,plain,
    ( sP1(X0_54,X1_54,X0_53,X2_54,X3_54)
    | ~ r4_tsep_1(X1_54,X0_54,X2_54)
    | ~ v1_funct_2(X0_53,u1_struct_0(X1_54),u1_struct_0(X3_54))
    | ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X2_54,X1_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X3_54))))
    | v2_struct_0(X3_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X2_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X3_54)
    | ~ l1_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_2664,plain,
    ( sP1(sK5,sK2,X0_53,sK6,X0_54)
    | ~ r4_tsep_1(sK2,sK5,sK6)
    | ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_54))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK6,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0_53) ),
    inference(instantiation,[status(thm)],[c_880])).

cnf(c_2665,plain,
    ( sP1(sK5,sK2,X0_53,sK6,X0_54) = iProver_top
    | r4_tsep_1(sK2,sK5,sK6) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2664])).

cnf(c_2667,plain,
    ( sP1(sK5,sK2,sK4,sK6,sK3) = iProver_top
    | r4_tsep_1(sK2,sK5,sK6) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2665])).

cnf(c_906,plain,
    ( ~ l1_pre_topc(X0_54)
    | l1_struct_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2731,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_906])).

cnf(c_2732,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2731])).

cnf(c_44,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_875,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(subtyping,[status(esa)],[c_44])).

cnf(c_1873,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_875])).

cnf(c_110,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_13,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_895,plain,
    ( ~ v5_pre_topc(X0_53,X0_54,X1_54)
    | ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X0_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X2_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k2_tmap_1(X0_54,X1_54,X0_53,X2_54)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2617,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(X0_54)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_895])).

cnf(c_2735,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK6,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK6)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2617])).

cnf(c_2736,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2735])).

cnf(c_2775,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1873,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,c_89,c_90,c_110,c_2736])).

cnf(c_60,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_871,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_60])).

cnf(c_1877,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_871])).

cnf(c_94,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_2738,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2617])).

cnf(c_2739,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2738])).

cnf(c_2905,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1877,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,c_87,c_88,c_94,c_2739])).

cnf(c_36,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_877,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_1871,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_877])).

cnf(c_118,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_11,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(k2_tmap_1(X1,X2,X0,X3),X3,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_897,plain,
    ( ~ v5_pre_topc(X0_53,X0_54,X1_54)
    | v5_pre_topc(k2_tmap_1(X0_54,X1_54,X0_53,X2_54),X2_54,X1_54)
    | ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X0_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X2_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2659,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_54),X0_54,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(X0_54)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_897])).

cnf(c_2815,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK6,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK6)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2659])).

cnf(c_2816,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2815])).

cnf(c_2911,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1871,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,c_89,c_90,c_118,c_2816])).

cnf(c_52,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_873,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_52])).

cnf(c_1875,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_873])).

cnf(c_102,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_2818,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2659])).

cnf(c_2819,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2818])).

cnf(c_3028,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1875,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,c_87,c_88,c_102,c_2819])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_905,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_868,negated_conjecture,
    ( m1_pre_topc(sK6,sK2) ),
    inference(subtyping,[status(esa)],[c_65])).

cnf(c_3052,plain,
    ( l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_905,c_868])).

cnf(c_3057,plain,
    ( l1_pre_topc(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3052,c_75])).

cnf(c_3361,plain,
    ( l1_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_3057,c_906])).

cnf(c_3362,plain,
    ( l1_struct_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3361])).

cnf(c_40,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_876,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_40])).

cnf(c_1872,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_876])).

cnf(c_114,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_12,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_896,plain,
    ( ~ v5_pre_topc(X0_53,X0_54,X1_54)
    | ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | v1_funct_2(k2_tmap_1(X0_54,X1_54,X0_53,X2_54),u1_struct_0(X2_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X0_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X2_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2654,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_54),u1_struct_0(X0_54),u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(X0_54)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_896])).

cnf(c_2758,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK6,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK6)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2654])).

cnf(c_2759,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2758])).

cnf(c_3390,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1872,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,c_89,c_90,c_114,c_2759])).

cnf(c_56,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_872,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_56])).

cnf(c_1876,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_872])).

cnf(c_98,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_2761,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2654])).

cnf(c_2762,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2761])).

cnf(c_3396,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1876,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,c_87,c_88,c_98,c_2762])).

cnf(c_866,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(subtyping,[status(esa)],[c_67])).

cnf(c_3054,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_905,c_866])).

cnf(c_3364,plain,
    ( l1_pre_topc(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3054,c_75])).

cnf(c_3405,plain,
    ( l1_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_3364,c_906])).

cnf(c_3406,plain,
    ( l1_struct_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3405])).

cnf(c_3127,plain,
    ( sP0(sK3,X0_54,sK4,sK2,sK5)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_54),X0_54,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_54),u1_struct_0(X0_54),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_889])).

cnf(c_4219,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_3127])).

cnf(c_4220,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4219])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_900,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | m1_subset_1(k2_tmap_1(X0_54,X1_54,X0_53,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | ~ l1_struct_0(X2_54)
    | ~ l1_struct_0(X1_54)
    | ~ l1_struct_0(X0_54)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2612,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(X0_54)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_900])).

cnf(c_4468,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2612])).

cnf(c_4469,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4468])).

cnf(c_4537,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK6)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2612])).

cnf(c_4538,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4537])).

cnf(c_4858,plain,
    ( sP1(sK5,sK2,sK4,sK6,sK3) != iProver_top
    | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4856])).

cnf(c_3195,plain,
    ( sP0(sK3,X0_54,sK4,sK2,sK6)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_54),X0_54,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_54),u1_struct_0(X0_54),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_889])).

cnf(c_5050,plain,
    ( sP0(sK3,sK2,sK4,sK2,sK6)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) ),
    inference(instantiation,[status(thm)],[c_3195])).

cnf(c_5056,plain,
    ( sP0(sK3,sK2,sK4,sK2,sK6) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5050])).

cnf(c_5844,plain,
    ( sP1(sK5,sK2,sK4,sK6,sK3) != iProver_top
    | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5841])).

cnf(c_6010,plain,
    ( sP1(sK5,sK2,sK4,sK6,sK3) != iProver_top
    | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6007])).

cnf(c_7217,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2612])).

cnf(c_7218,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7217])).

cnf(c_13543,plain,
    ( sP0(sK3,sK2,sK4,sK2,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13357,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,c_87,c_88,c_89,c_90,c_91,c_94,c_98,c_102,c_110,c_114,c_118,c_198,c_2667,c_2732,c_2736,c_2739,c_2759,c_2762,c_2816,c_2819,c_3362,c_3406,c_4220,c_4469,c_4538,c_4858,c_5056,c_5844,c_6010,c_7218])).

cnf(c_20,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_888,plain,
    ( ~ sP0(X0_54,X1_54,X0_53,X2_54,X3_54)
    | m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_53,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1860,plain,
    ( sP0(X0_54,X1_54,X0_53,X2_54,X3_54) != iProver_top
    | m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_53,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_888])).

cnf(c_13549,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13543,c_1860])).

cnf(c_864,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_69])).

cnf(c_1883,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_864])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_907,plain,
    ( ~ r2_funct_2(X0_55,X1_55,X0_53,X1_53)
    | ~ v1_funct_2(X1_53,X0_55,X1_55)
    | ~ v1_funct_2(X0_53,X0_55,X1_55)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | X0_53 = X1_53 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1841,plain,
    ( X0_53 = X1_53
    | r2_funct_2(X0_55,X1_55,X0_53,X1_53) != iProver_top
    | v1_funct_2(X0_53,X0_55,X1_55) != iProver_top
    | v1_funct_2(X1_53,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_907])).

cnf(c_3042,plain,
    ( sK4 = X0_53
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_53) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1883,c_1841])).

cnf(c_4240,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | sK4 = X0_53
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_53) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3042,c_84,c_85])).

cnf(c_4241,plain,
    ( sK4 = X0_53
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_53) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_4240])).

cnf(c_14892,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13549,c_4241])).

cnf(c_916,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_911,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_3837,plain,
    ( X0_54 != X1_54
    | X1_54 = X0_54 ),
    inference(resolution,[status(thm)],[c_916,c_911])).

cnf(c_4568,plain,
    ( sK2 = k1_tsep_1(sK2,sK5,sK6) ),
    inference(resolution,[status(thm)],[c_3837,c_869])).

cnf(c_924,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | m1_pre_topc(X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_4749,plain,
    ( ~ m1_pre_topc(X0_54,k1_tsep_1(sK2,sK5,sK6))
    | m1_pre_topc(X1_54,sK2)
    | X1_54 != X0_54 ),
    inference(resolution,[status(thm)],[c_4568,c_924])).

cnf(c_3993,plain,
    ( m1_pre_topc(X0_54,k1_tsep_1(sK2,sK5,sK6))
    | ~ m1_pre_topc(X1_54,sK2)
    | X0_54 != X1_54 ),
    inference(resolution,[status(thm)],[c_924,c_869])).

cnf(c_4167,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),k1_tsep_1(sK2,sK5,sK6))
    | ~ m1_pre_topc(sK2,sK2) ),
    inference(resolution,[status(thm)],[c_3993,c_869])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_902,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X2_54,X1_54)
    | m1_pre_topc(k1_tsep_1(X1_54,X0_54,X2_54),X1_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X2_54)
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2573,plain,
    ( ~ m1_pre_topc(X0_54,sK2)
    | m1_pre_topc(k1_tsep_1(sK2,X0_54,sK6),sK2)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK6)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_902])).

cnf(c_2722,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2573])).

cnf(c_2876,plain,
    ( m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2)
    | X0_54 != k1_tsep_1(sK2,sK5,sK6)
    | X1_54 != sK2 ),
    inference(instantiation,[status(thm)],[c_924])).

cnf(c_3620,plain,
    ( m1_pre_topc(X0_54,k1_tsep_1(sK2,sK5,sK6))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2)
    | X0_54 != k1_tsep_1(sK2,sK5,sK6)
    | k1_tsep_1(sK2,sK5,sK6) != sK2 ),
    inference(instantiation,[status(thm)],[c_2876])).

cnf(c_3863,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),k1_tsep_1(sK2,sK5,sK6))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2)
    | k1_tsep_1(sK2,sK5,sK6) != k1_tsep_1(sK2,sK5,sK6)
    | k1_tsep_1(sK2,sK5,sK6) != sK2 ),
    inference(instantiation,[status(thm)],[c_3620])).

cnf(c_3864,plain,
    ( k1_tsep_1(sK2,sK5,sK6) = k1_tsep_1(sK2,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_911])).

cnf(c_4178,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),k1_tsep_1(sK2,sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4167,c_77,c_75,c_68,c_67,c_66,c_65,c_869,c_2722,c_3863,c_3864])).

cnf(c_5299,plain,
    ( m1_pre_topc(X0_54,sK2)
    | X0_54 != k1_tsep_1(sK2,sK5,sK6) ),
    inference(resolution,[status(thm)],[c_4749,c_4178])).

cnf(c_5321,plain,
    ( m1_pre_topc(sK2,sK2) ),
    inference(resolution,[status(thm)],[c_5299,c_4568])).

cnf(c_5322,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5321])).

cnf(c_8263,plain,
    ( k2_tmap_1(sK2,sK3,X0_53,sK2) = sK4
    | sP1(sK5,sK2,X0_53,sK6,sK3) != iProver_top
    | sP0(sK3,sK6,X0_53,sK2,sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,X0_53,sK2)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,X0_53,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7927,c_4241])).

cnf(c_8730,plain,
    ( k2_tmap_1(sK2,sK3,X0_53,sK2) = sK4
    | sP1(sK5,sK2,X0_53,sK6,sK3) != iProver_top
    | sP0(sK3,sK6,X0_53,sK2,sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,X0_53,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8263,c_4856,c_6007])).

cnf(c_8732,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4
    | sP1(sK5,sK2,sK4,sK6,sK3) != iProver_top
    | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8730])).

cnf(c_1846,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1_54,X0_54,X2_54),X1_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_902])).

cnf(c_5512,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_869,c_1846])).

cnf(c_6308,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5512,c_5322])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_903,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X0_54,X2_54)
    | ~ m1_pre_topc(X3_54,X0_54)
    | ~ m1_pre_topc(X3_54,X2_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | v2_struct_0(X2_54)
    | v2_struct_0(X1_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X2_54)
    | ~ l1_pre_topc(X2_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_53,u1_struct_0(X3_54)) = k3_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1845,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_53,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_53)
    | v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_903])).

cnf(c_4651,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK3,sK2,X0_54,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1883,c_1845])).

cnf(c_5164,plain,
    ( v2_pre_topc(X1_54) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK3,sK2,X0_54,sK4)
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4651,c_81,c_82,c_83,c_84,c_85])).

cnf(c_5165,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK3,sK2,X0_54,sK4)
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_5164])).

cnf(c_6314,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK2,sK3,sK2,sK2,sK4)
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6308,c_5165])).

cnf(c_4,plain,
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

cnf(c_904,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X0_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_53,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_53,X2_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1844,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_53,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_53,X2_54)
    | v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_904])).

cnf(c_3747,plain,
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
    inference(superposition,[status(thm)],[c_1883,c_1844])).

cnf(c_4478,plain,
    ( m1_pre_topc(X0_54,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK3,sK4,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3747,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85])).

cnf(c_4479,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK3,sK4,X0_54)
    | m1_pre_topc(X0_54,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4478])).

cnf(c_6316,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK3,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_6308,c_4479])).

cnf(c_6319,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK2,sK4) = k2_tmap_1(sK2,sK3,sK4,sK2)
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6314,c_6316])).

cnf(c_6325,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK2,sK4) = k2_tmap_1(sK2,sK3,sK4,sK2)
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6319,c_6308])).

cnf(c_6694,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK2,sK4) = k2_tmap_1(sK2,sK3,sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6325,c_78,c_79,c_80])).

cnf(c_29,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_879,plain,
    ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_53,k3_tmap_1(X2_54,X1_54,X0_54,X0_54,X0_53))
    | ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X0_54,X2_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X2_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X2_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X2_54)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1869,plain,
    ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_53,k3_tmap_1(X2_54,X1_54,X0_54,X0_54,X0_53)) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_879])).

cnf(c_9329,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6694,c_1869])).

cnf(c_15737,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14892,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,c_87,c_88,c_89,c_90,c_91,c_94,c_98,c_102,c_110,c_114,c_118,c_198,c_2667,c_2732,c_2736,c_2739,c_2759,c_2762,c_2816,c_2819,c_3362,c_3406,c_4220,c_4469,c_4538,c_5322,c_8732,c_9329])).

cnf(c_21,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_887,plain,
    ( ~ sP0(X0_54,X1_54,X0_53,X2_54,X3_54)
    | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_53,X1_54),X1_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1861,plain,
    ( sP0(X0_54,X1_54,X0_53,X2_54,X3_54) != iProver_top
    | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_53,X1_54),X1_54,X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_887])).

cnf(c_13553,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_13543,c_1861])).

cnf(c_15743,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15737,c_13553])).

cnf(c_30,negated_conjecture,
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

cnf(c_582,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30,c_71,c_70,c_69])).

cnf(c_583,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(renaming,[status(thm)],[c_582])).

cnf(c_855,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(subtyping,[status(esa)],[c_583])).

cnf(c_1892,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_855])).

cnf(c_584,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_2765,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1892,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,c_87,c_88,c_89,c_90,c_94,c_98,c_110,c_114,c_584,c_2736,c_2739,c_2759,c_2762])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15743,c_4538,c_4469,c_3406,c_3362,c_3028,c_2911,c_2765,c_2732,c_198,c_86,c_85,c_84,c_83,c_80])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.43/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.43/1.49  
% 7.43/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.43/1.49  
% 7.43/1.49  ------  iProver source info
% 7.43/1.49  
% 7.43/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.43/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.43/1.49  git: non_committed_changes: false
% 7.43/1.49  git: last_make_outside_of_git: false
% 7.43/1.49  
% 7.43/1.49  ------ 
% 7.43/1.49  ------ Parsing...
% 7.43/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.43/1.49  
% 7.43/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.43/1.49  
% 7.43/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.43/1.49  
% 7.43/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.43/1.49  ------ Proving...
% 7.43/1.49  ------ Problem Properties 
% 7.43/1.49  
% 7.43/1.49  
% 7.43/1.49  clauses                                 54
% 7.43/1.49  conjectures                             24
% 7.43/1.49  EPR                                     14
% 7.43/1.49  Horn                                    37
% 7.43/1.49  unary                                   15
% 7.43/1.49  binary                                  17
% 7.43/1.49  lits                                    225
% 7.43/1.49  lits eq                                 4
% 7.43/1.49  fd_pure                                 0
% 7.43/1.49  fd_pseudo                               0
% 7.43/1.49  fd_cond                                 0
% 7.43/1.49  fd_pseudo_cond                          1
% 7.43/1.49  AC symbols                              0
% 7.43/1.49  
% 7.43/1.49  ------ Input Options Time Limit: Unbounded
% 7.43/1.49  
% 7.43/1.49  
% 7.43/1.49  ------ 
% 7.43/1.49  Current options:
% 7.43/1.49  ------ 
% 7.43/1.49  
% 7.43/1.49  
% 7.43/1.49  
% 7.43/1.49  
% 7.43/1.49  ------ Proving...
% 7.43/1.49  
% 7.43/1.49  
% 7.43/1.49  % SZS status Theorem for theBenchmark.p
% 7.43/1.49  
% 7.43/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.43/1.49  
% 7.43/1.49  fof(f11,conjecture,(
% 7.43/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 7.43/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f12,negated_conjecture,(
% 7.43/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 7.43/1.49    inference(negated_conjecture,[],[f11])).
% 7.43/1.49  
% 7.43/1.49  fof(f32,plain,(
% 7.43/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & (r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0)) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.43/1.49    inference(ennf_transformation,[],[f12])).
% 7.43/1.49  
% 7.43/1.49  fof(f33,plain,(
% 7.43/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.43/1.49    inference(flattening,[],[f32])).
% 7.43/1.49  
% 7.43/1.49  fof(f44,plain,(
% 7.43/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.43/1.49    inference(nnf_transformation,[],[f33])).
% 7.43/1.49  
% 7.43/1.49  fof(f45,plain,(
% 7.43/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.43/1.49    inference(flattening,[],[f44])).
% 7.43/1.49  
% 7.43/1.49  fof(f50,plain,(
% 7.43/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((~m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,sK6) & k1_tsep_1(X0,X3,sK6) = X0 & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 7.43/1.49    introduced(choice_axiom,[])).
% 7.43/1.49  
% 7.43/1.49  fof(f49,plain,(
% 7.43/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK5)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK5))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,sK5,X4) & k1_tsep_1(X0,sK5,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 7.43/1.49    introduced(choice_axiom,[])).
% 7.43/1.49  
% 7.43/1.49  fof(f48,plain,(
% 7.43/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(sK4,X0,X1) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) & m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X3))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK4,X0,X1) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 7.43/1.49    introduced(choice_axiom,[])).
% 7.43/1.49  
% 7.43/1.49  fof(f47,plain,(
% 7.43/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(X2,X0,sK3) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) & m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v5_pre_topc(X2,X0,sK3) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 7.43/1.49    introduced(choice_axiom,[])).
% 7.43/1.49  
% 7.43/1.49  fof(f46,plain,(
% 7.43/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(sK2,X3,X4) & k1_tsep_1(sK2,X3,X4) = sK2 & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 7.43/1.49    introduced(choice_axiom,[])).
% 7.43/1.49  
% 7.43/1.49  fof(f51,plain,(
% 7.43/1.49    (((((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,sK5,sK6) & k1_tsep_1(sK2,sK5,sK6) = sK2 & m1_pre_topc(sK6,sK2) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 7.43/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f45,f50,f49,f48,f47,f46])).
% 7.43/1.49  
% 7.43/1.49  fof(f127,plain,(
% 7.43/1.49    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f95,plain,(
% 7.43/1.49    k1_tsep_1(sK2,sK5,sK6) = sK2),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f35,plain,(
% 7.43/1.49    ! [X2,X0,X4,X3,X1] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> sP0(X1,X3,X4,X0,X2)) | ~sP1(X2,X0,X4,X3,X1))),
% 7.43/1.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 7.43/1.49  
% 7.43/1.49  fof(f38,plain,(
% 7.43/1.49    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))))) | ~sP1(X2,X0,X4,X3,X1))),
% 7.43/1.49    inference(nnf_transformation,[],[f35])).
% 7.43/1.49  
% 7.43/1.49  fof(f39,plain,(
% 7.43/1.49    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))))) | ~sP1(X2,X0,X4,X3,X1))),
% 7.43/1.49    inference(flattening,[],[f38])).
% 7.43/1.49  
% 7.43/1.49  fof(f40,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) & v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) & v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) & v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))))) | ~sP1(X0,X1,X2,X3,X4))),
% 7.43/1.49    inference(rectify,[],[f39])).
% 7.43/1.49  
% 7.43/1.49  fof(f70,plain,(
% 7.43/1.49    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f40])).
% 7.43/1.49  
% 7.43/1.49  fof(f34,plain,(
% 7.43/1.49    ! [X1,X3,X4,X0,X2] : (sP0(X1,X3,X4,X0,X2) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))),
% 7.43/1.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.43/1.49  
% 7.43/1.49  fof(f41,plain,(
% 7.43/1.49    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 7.43/1.49    inference(nnf_transformation,[],[f34])).
% 7.43/1.49  
% 7.43/1.49  fof(f42,plain,(
% 7.43/1.49    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 7.43/1.49    inference(flattening,[],[f41])).
% 7.43/1.49  
% 7.43/1.49  fof(f43,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) & ((m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 7.43/1.49    inference(rectify,[],[f42])).
% 7.43/1.49  
% 7.43/1.49  fof(f79,plain,(
% 7.43/1.49    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) )),
% 7.43/1.49    inference(cnf_transformation,[],[f43])).
% 7.43/1.49  
% 7.43/1.49  fof(f67,plain,(
% 7.43/1.49    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f40])).
% 7.43/1.49  
% 7.43/1.49  fof(f69,plain,(
% 7.43/1.49    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f40])).
% 7.43/1.49  
% 7.43/1.49  fof(f68,plain,(
% 7.43/1.49    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f40])).
% 7.43/1.49  
% 7.43/1.49  fof(f82,plain,(
% 7.43/1.49    ~v2_struct_0(sK2)),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f83,plain,(
% 7.43/1.49    v2_pre_topc(sK2)),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f84,plain,(
% 7.43/1.49    l1_pre_topc(sK2)),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f85,plain,(
% 7.43/1.49    ~v2_struct_0(sK3)),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f86,plain,(
% 7.43/1.49    v2_pre_topc(sK3)),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f87,plain,(
% 7.43/1.49    l1_pre_topc(sK3)),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f88,plain,(
% 7.43/1.49    v1_funct_1(sK4)),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f89,plain,(
% 7.43/1.49    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f90,plain,(
% 7.43/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f91,plain,(
% 7.43/1.49    ~v2_struct_0(sK5)),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f92,plain,(
% 7.43/1.49    m1_pre_topc(sK5,sK2)),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f93,plain,(
% 7.43/1.49    ~v2_struct_0(sK6)),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f94,plain,(
% 7.43/1.49    m1_pre_topc(sK6,sK2)),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f96,plain,(
% 7.43/1.49    r4_tsep_1(sK2,sK5,sK6)),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f2,axiom,(
% 7.43/1.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.43/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f16,plain,(
% 7.43/1.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.43/1.49    inference(ennf_transformation,[],[f2])).
% 7.43/1.49  
% 7.43/1.49  fof(f54,plain,(
% 7.43/1.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f16])).
% 7.43/1.49  
% 7.43/1.49  fof(f9,axiom,(
% 7.43/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))))))))),
% 7.43/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f28,plain,(
% 7.43/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.43/1.49    inference(ennf_transformation,[],[f9])).
% 7.43/1.49  
% 7.43/1.49  fof(f29,plain,(
% 7.43/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.43/1.49    inference(flattening,[],[f28])).
% 7.43/1.49  
% 7.43/1.49  fof(f36,plain,(
% 7.43/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X2,X0,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.43/1.49    inference(definition_folding,[],[f29,f35,f34])).
% 7.43/1.49  
% 7.43/1.49  fof(f80,plain,(
% 7.43/1.49    ( ! [X4,X2,X0,X3,X1] : (sP1(X2,X0,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f36])).
% 7.43/1.49  
% 7.43/1.49  fof(f115,plain,(
% 7.43/1.49    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | v5_pre_topc(sK4,sK2,sK3)),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f8,axiom,(
% 7.43/1.49    ! [X0,X1,X2,X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 7.43/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f26,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.43/1.49    inference(ennf_transformation,[],[f8])).
% 7.43/1.49  
% 7.43/1.49  fof(f27,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.43/1.49    inference(flattening,[],[f26])).
% 7.43/1.49  
% 7.43/1.49  fof(f63,plain,(
% 7.43/1.49    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f27])).
% 7.43/1.49  
% 7.43/1.49  fof(f99,plain,(
% 7.43/1.49    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | v5_pre_topc(sK4,sK2,sK3)),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f123,plain,(
% 7.43/1.49    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f65,plain,(
% 7.43/1.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f27])).
% 7.43/1.49  
% 7.43/1.49  fof(f107,plain,(
% 7.43/1.49    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f3,axiom,(
% 7.43/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.43/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f17,plain,(
% 7.43/1.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.43/1.49    inference(ennf_transformation,[],[f3])).
% 7.43/1.49  
% 7.43/1.49  fof(f55,plain,(
% 7.43/1.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f17])).
% 7.43/1.49  
% 7.43/1.49  fof(f119,plain,(
% 7.43/1.49    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f64,plain,(
% 7.43/1.49    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f27])).
% 7.43/1.49  
% 7.43/1.49  fof(f103,plain,(
% 7.43/1.49    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f7,axiom,(
% 7.43/1.49    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 7.43/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f24,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 7.43/1.49    inference(ennf_transformation,[],[f7])).
% 7.43/1.49  
% 7.43/1.49  fof(f25,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 7.43/1.49    inference(flattening,[],[f24])).
% 7.43/1.49  
% 7.43/1.49  fof(f62,plain,(
% 7.43/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f25])).
% 7.43/1.49  
% 7.43/1.49  fof(f78,plain,(
% 7.43/1.49    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP0(X0,X1,X2,X3,X4)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f43])).
% 7.43/1.49  
% 7.43/1.49  fof(f1,axiom,(
% 7.43/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 7.43/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f14,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.43/1.49    inference(ennf_transformation,[],[f1])).
% 7.43/1.49  
% 7.43/1.49  fof(f15,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.43/1.49    inference(flattening,[],[f14])).
% 7.43/1.49  
% 7.43/1.49  fof(f37,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.43/1.49    inference(nnf_transformation,[],[f15])).
% 7.43/1.49  
% 7.43/1.49  fof(f52,plain,(
% 7.43/1.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f37])).
% 7.43/1.49  
% 7.43/1.49  fof(f6,axiom,(
% 7.43/1.49    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 7.43/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f13,plain,(
% 7.43/1.49    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 7.43/1.49    inference(pure_predicate_removal,[],[f6])).
% 7.43/1.49  
% 7.43/1.49  fof(f22,plain,(
% 7.43/1.49    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.43/1.49    inference(ennf_transformation,[],[f13])).
% 7.43/1.49  
% 7.43/1.49  fof(f23,plain,(
% 7.43/1.49    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.43/1.49    inference(flattening,[],[f22])).
% 7.43/1.49  
% 7.43/1.49  fof(f59,plain,(
% 7.43/1.49    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f23])).
% 7.43/1.49  
% 7.43/1.49  fof(f5,axiom,(
% 7.43/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 7.43/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f20,plain,(
% 7.43/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.43/1.49    inference(ennf_transformation,[],[f5])).
% 7.43/1.49  
% 7.43/1.49  fof(f21,plain,(
% 7.43/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.43/1.49    inference(flattening,[],[f20])).
% 7.43/1.49  
% 7.43/1.49  fof(f57,plain,(
% 7.43/1.49    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f21])).
% 7.43/1.49  
% 7.43/1.49  fof(f4,axiom,(
% 7.43/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 7.43/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f18,plain,(
% 7.43/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.43/1.49    inference(ennf_transformation,[],[f4])).
% 7.43/1.49  
% 7.43/1.49  fof(f19,plain,(
% 7.43/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.43/1.49    inference(flattening,[],[f18])).
% 7.43/1.49  
% 7.43/1.49  fof(f56,plain,(
% 7.43/1.49    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f19])).
% 7.43/1.49  
% 7.43/1.49  fof(f10,axiom,(
% 7.43/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 7.43/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f30,plain,(
% 7.43/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.43/1.49    inference(ennf_transformation,[],[f10])).
% 7.43/1.49  
% 7.43/1.49  fof(f31,plain,(
% 7.43/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.43/1.49    inference(flattening,[],[f30])).
% 7.43/1.49  
% 7.43/1.49  fof(f81,plain,(
% 7.43/1.49    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f31])).
% 7.43/1.49  
% 7.43/1.49  fof(f77,plain,(
% 7.43/1.49    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f43])).
% 7.43/1.49  
% 7.43/1.49  fof(f129,plain,(
% 7.43/1.49    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 7.43/1.49    inference(cnf_transformation,[],[f51])).
% 7.43/1.49  
% 7.43/1.49  cnf(c_32,negated_conjecture,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 7.43/1.49      inference(cnf_transformation,[],[f127]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_878,negated_conjecture,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_32]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1870,plain,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_878]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_64,negated_conjecture,
% 7.43/1.49      ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
% 7.43/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_869,negated_conjecture,
% 7.43/1.49      ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_64]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_14,plain,
% 7.43/1.49      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.43/1.49      | ~ sP0(X4,X3,X2,X1,X0)
% 7.43/1.49      | m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) ),
% 7.43/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_894,plain,
% 7.43/1.49      ( ~ sP1(X0_54,X1_54,X0_53,X2_54,X3_54)
% 7.43/1.49      | ~ sP0(X3_54,X2_54,X0_53,X1_54,X0_54)
% 7.43/1.49      | m1_subset_1(k2_tmap_1(X1_54,X3_54,X0_53,k1_tsep_1(X1_54,X0_54,X2_54)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_54,X0_54,X2_54)),u1_struct_0(X3_54)))) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_14]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1854,plain,
% 7.43/1.49      ( sP1(X0_54,X1_54,X0_53,X2_54,X3_54) != iProver_top
% 7.43/1.49      | sP0(X3_54,X2_54,X0_53,X1_54,X0_54) != iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(X1_54,X3_54,X0_53,k1_tsep_1(X1_54,X0_54,X2_54)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_54,X0_54,X2_54)),u1_struct_0(X3_54)))) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_894]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_7927,plain,
% 7.43/1.49      ( sP1(sK5,sK2,X0_53,sK6,X0_54) != iProver_top
% 7.43/1.49      | sP0(X0_54,sK6,X0_53,sK2,sK5) != iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_53,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) = iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_869,c_1854]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_19,plain,
% 7.43/1.49      ( sP0(X0,X1,X2,X3,X4)
% 7.43/1.49      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
% 7.43/1.49      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
% 7.43/1.49      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
% 7.43/1.49      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
% 7.43/1.49      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 7.43/1.49      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
% 7.43/1.49      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
% 7.43/1.49      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
% 7.43/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_889,plain,
% 7.43/1.49      ( sP0(X0_54,X1_54,X0_53,X2_54,X3_54)
% 7.43/1.49      | ~ v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_53,X1_54),X1_54,X0_54)
% 7.43/1.49      | ~ v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_53,X3_54),X3_54,X0_54)
% 7.43/1.49      | ~ v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_53,X1_54),u1_struct_0(X1_54),u1_struct_0(X0_54))
% 7.43/1.49      | ~ v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_53,X3_54),u1_struct_0(X3_54),u1_struct_0(X0_54))
% 7.43/1.49      | ~ m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_53,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54))))
% 7.43/1.49      | ~ m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_53,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X0_54))))
% 7.43/1.49      | ~ v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_53,X1_54))
% 7.43/1.49      | ~ v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_53,X3_54)) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_19]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1859,plain,
% 7.43/1.49      ( sP0(X0_54,X1_54,X0_53,X2_54,X3_54) = iProver_top
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_53,X1_54),X1_54,X0_54) != iProver_top
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_53,X3_54),X3_54,X0_54) != iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_53,X1_54),u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_53,X3_54),u1_struct_0(X3_54),u1_struct_0(X0_54)) != iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_53,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_53,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X0_54)))) != iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_53,X1_54)) != iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_53,X3_54)) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_889]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_11684,plain,
% 7.43/1.49      ( sP1(sK5,sK2,X0_53,sK6,X0_54) != iProver_top
% 7.43/1.49      | sP0(X0_54,sK6,X0_53,sK2,sK5) != iProver_top
% 7.43/1.49      | sP0(X0_54,sK2,X0_53,sK2,X1_54) = iProver_top
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_53,X1_54),X1_54,X0_54) != iProver_top
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_53,sK2),sK2,X0_54) != iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_53,X1_54),u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_53,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_53,X1_54)) != iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_53,sK2)) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_7927,c_1859]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_17,plain,
% 7.43/1.49      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.43/1.49      | ~ sP0(X4,X3,X2,X1,X0)
% 7.43/1.49      | v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
% 7.43/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_891,plain,
% 7.43/1.49      ( ~ sP1(X0_54,X1_54,X0_53,X2_54,X3_54)
% 7.43/1.49      | ~ sP0(X3_54,X2_54,X0_53,X1_54,X0_54)
% 7.43/1.49      | v1_funct_1(k2_tmap_1(X1_54,X3_54,X0_53,k1_tsep_1(X1_54,X0_54,X2_54))) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_17]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1857,plain,
% 7.43/1.49      ( sP1(X0_54,X1_54,X0_53,X2_54,X3_54) != iProver_top
% 7.43/1.49      | sP0(X3_54,X2_54,X0_53,X1_54,X0_54) != iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(X1_54,X3_54,X0_53,k1_tsep_1(X1_54,X0_54,X2_54))) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_891]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4856,plain,
% 7.43/1.49      ( sP1(sK5,sK2,X0_53,sK6,X0_54) != iProver_top
% 7.43/1.49      | sP0(X0_54,sK6,X0_53,sK2,sK5) != iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_53,sK2)) = iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_869,c_1857]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_15,plain,
% 7.43/1.49      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.43/1.49      | ~ sP0(X4,X3,X2,X1,X0)
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) ),
% 7.43/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_893,plain,
% 7.43/1.49      ( ~ sP1(X0_54,X1_54,X0_53,X2_54,X3_54)
% 7.43/1.49      | ~ sP0(X3_54,X2_54,X0_53,X1_54,X0_54)
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(X1_54,X3_54,X0_53,k1_tsep_1(X1_54,X0_54,X2_54)),k1_tsep_1(X1_54,X0_54,X2_54),X3_54) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_15]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1855,plain,
% 7.43/1.49      ( sP1(X0_54,X1_54,X0_53,X2_54,X3_54) != iProver_top
% 7.43/1.49      | sP0(X3_54,X2_54,X0_53,X1_54,X0_54) != iProver_top
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(X1_54,X3_54,X0_53,k1_tsep_1(X1_54,X0_54,X2_54)),k1_tsep_1(X1_54,X0_54,X2_54),X3_54) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_893]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_5841,plain,
% 7.43/1.49      ( sP1(sK5,sK2,X0_53,sK6,X0_54) != iProver_top
% 7.43/1.49      | sP0(X0_54,sK6,X0_53,sK2,sK5) != iProver_top
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_53,sK2),sK2,X0_54) = iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_869,c_1855]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_16,plain,
% 7.43/1.49      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.43/1.49      | ~ sP0(X4,X3,X2,X1,X0)
% 7.43/1.49      | v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) ),
% 7.43/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_892,plain,
% 7.43/1.49      ( ~ sP1(X0_54,X1_54,X0_53,X2_54,X3_54)
% 7.43/1.49      | ~ sP0(X3_54,X2_54,X0_53,X1_54,X0_54)
% 7.43/1.49      | v1_funct_2(k2_tmap_1(X1_54,X3_54,X0_53,k1_tsep_1(X1_54,X0_54,X2_54)),u1_struct_0(k1_tsep_1(X1_54,X0_54,X2_54)),u1_struct_0(X3_54)) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_16]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1856,plain,
% 7.43/1.49      ( sP1(X0_54,X1_54,X0_53,X2_54,X3_54) != iProver_top
% 7.43/1.49      | sP0(X3_54,X2_54,X0_53,X1_54,X0_54) != iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(X1_54,X3_54,X0_53,k1_tsep_1(X1_54,X0_54,X2_54)),u1_struct_0(k1_tsep_1(X1_54,X0_54,X2_54)),u1_struct_0(X3_54)) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_892]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6007,plain,
% 7.43/1.49      ( sP1(sK5,sK2,X0_53,sK6,X0_54) != iProver_top
% 7.43/1.49      | sP0(X0_54,sK6,X0_53,sK2,sK5) != iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) = iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_869,c_1856]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_13344,plain,
% 7.43/1.49      ( v1_funct_1(k2_tmap_1(sK2,X0_54,X0_53,X1_54)) != iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_53,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_53,X1_54),X1_54,X0_54) != iProver_top
% 7.43/1.49      | sP0(X0_54,sK2,X0_53,sK2,X1_54) = iProver_top
% 7.43/1.49      | sP0(X0_54,sK6,X0_53,sK2,sK5) != iProver_top
% 7.43/1.49      | sP1(sK5,sK2,X0_53,sK6,X0_54) != iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_53,X1_54),u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_11684,c_4856,c_5841,c_6007]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_13345,plain,
% 7.43/1.49      ( sP1(sK5,sK2,X0_53,sK6,X0_54) != iProver_top
% 7.43/1.49      | sP0(X0_54,sK6,X0_53,sK2,sK5) != iProver_top
% 7.43/1.49      | sP0(X0_54,sK2,X0_53,sK2,X1_54) = iProver_top
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_53,X1_54),X1_54,X0_54) != iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_53,X1_54),u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_53,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_53,X1_54)) != iProver_top ),
% 7.43/1.49      inference(renaming,[status(thm)],[c_13344]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_13357,plain,
% 7.43/1.49      ( sP1(sK5,sK2,sK4,sK6,sK3) != iProver_top
% 7.43/1.49      | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.43/1.49      | sP0(sK3,sK2,sK4,sK2,sK6) = iProver_top
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.43/1.49      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_1870,c_13345]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_77,negated_conjecture,
% 7.43/1.49      ( ~ v2_struct_0(sK2) ),
% 7.43/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_78,plain,
% 7.43/1.49      ( v2_struct_0(sK2) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_77]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_76,negated_conjecture,
% 7.43/1.49      ( v2_pre_topc(sK2) ),
% 7.43/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_79,plain,
% 7.43/1.49      ( v2_pre_topc(sK2) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_76]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_75,negated_conjecture,
% 7.43/1.49      ( l1_pre_topc(sK2) ),
% 7.43/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_80,plain,
% 7.43/1.49      ( l1_pre_topc(sK2) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_75]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_74,negated_conjecture,
% 7.43/1.49      ( ~ v2_struct_0(sK3) ),
% 7.43/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_81,plain,
% 7.43/1.49      ( v2_struct_0(sK3) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_74]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_73,negated_conjecture,
% 7.43/1.49      ( v2_pre_topc(sK3) ),
% 7.43/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_82,plain,
% 7.43/1.49      ( v2_pre_topc(sK3) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_73]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_72,negated_conjecture,
% 7.43/1.49      ( l1_pre_topc(sK3) ),
% 7.43/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_83,plain,
% 7.43/1.49      ( l1_pre_topc(sK3) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_72]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_71,negated_conjecture,
% 7.43/1.49      ( v1_funct_1(sK4) ),
% 7.43/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_84,plain,
% 7.43/1.49      ( v1_funct_1(sK4) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_71]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_70,negated_conjecture,
% 7.43/1.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 7.43/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_85,plain,
% 7.43/1.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_70]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_69,negated_conjecture,
% 7.43/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 7.43/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_86,plain,
% 7.43/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_69]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_68,negated_conjecture,
% 7.43/1.49      ( ~ v2_struct_0(sK5) ),
% 7.43/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_87,plain,
% 7.43/1.49      ( v2_struct_0(sK5) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_68]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_67,negated_conjecture,
% 7.43/1.49      ( m1_pre_topc(sK5,sK2) ),
% 7.43/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_88,plain,
% 7.43/1.49      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_67]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_66,negated_conjecture,
% 7.43/1.49      ( ~ v2_struct_0(sK6) ),
% 7.43/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_89,plain,
% 7.43/1.49      ( v2_struct_0(sK6) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_66]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_65,negated_conjecture,
% 7.43/1.49      ( m1_pre_topc(sK6,sK2) ),
% 7.43/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_90,plain,
% 7.43/1.49      ( m1_pre_topc(sK6,sK2) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_65]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_63,negated_conjecture,
% 7.43/1.49      ( r4_tsep_1(sK2,sK5,sK6) ),
% 7.43/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_91,plain,
% 7.43/1.49      ( r4_tsep_1(sK2,sK5,sK6) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_63]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2,plain,
% 7.43/1.49      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.43/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_196,plain,
% 7.43/1.49      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_198,plain,
% 7.43/1.49      ( l1_pre_topc(sK3) != iProver_top
% 7.43/1.49      | l1_struct_0(sK3) = iProver_top ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_196]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_28,plain,
% 7.43/1.49      ( sP1(X0,X1,X2,X3,X4)
% 7.43/1.49      | ~ r4_tsep_1(X1,X0,X3)
% 7.43/1.49      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
% 7.43/1.49      | ~ m1_pre_topc(X3,X1)
% 7.43/1.49      | ~ m1_pre_topc(X0,X1)
% 7.43/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 7.43/1.49      | v2_struct_0(X1)
% 7.43/1.49      | v2_struct_0(X4)
% 7.43/1.49      | v2_struct_0(X3)
% 7.43/1.49      | v2_struct_0(X0)
% 7.43/1.49      | ~ v2_pre_topc(X4)
% 7.43/1.49      | ~ v2_pre_topc(X1)
% 7.43/1.49      | ~ l1_pre_topc(X1)
% 7.43/1.49      | ~ l1_pre_topc(X4)
% 7.43/1.49      | ~ v1_funct_1(X2) ),
% 7.43/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_880,plain,
% 7.43/1.49      ( sP1(X0_54,X1_54,X0_53,X2_54,X3_54)
% 7.43/1.49      | ~ r4_tsep_1(X1_54,X0_54,X2_54)
% 7.43/1.49      | ~ v1_funct_2(X0_53,u1_struct_0(X1_54),u1_struct_0(X3_54))
% 7.43/1.49      | ~ m1_pre_topc(X0_54,X1_54)
% 7.43/1.49      | ~ m1_pre_topc(X2_54,X1_54)
% 7.43/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X3_54))))
% 7.43/1.49      | v2_struct_0(X3_54)
% 7.43/1.49      | v2_struct_0(X1_54)
% 7.43/1.49      | v2_struct_0(X0_54)
% 7.43/1.49      | v2_struct_0(X2_54)
% 7.43/1.49      | ~ v2_pre_topc(X1_54)
% 7.43/1.49      | ~ v2_pre_topc(X3_54)
% 7.43/1.49      | ~ l1_pre_topc(X3_54)
% 7.43/1.49      | ~ l1_pre_topc(X1_54)
% 7.43/1.49      | ~ v1_funct_1(X0_53) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_28]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2664,plain,
% 7.43/1.49      ( sP1(sK5,sK2,X0_53,sK6,X0_54)
% 7.43/1.49      | ~ r4_tsep_1(sK2,sK5,sK6)
% 7.43/1.49      | ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_54))
% 7.43/1.49      | ~ m1_pre_topc(sK5,sK2)
% 7.43/1.49      | ~ m1_pre_topc(sK6,sK2)
% 7.43/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
% 7.43/1.49      | v2_struct_0(X0_54)
% 7.43/1.49      | v2_struct_0(sK5)
% 7.43/1.49      | v2_struct_0(sK6)
% 7.43/1.49      | v2_struct_0(sK2)
% 7.43/1.49      | ~ v2_pre_topc(X0_54)
% 7.43/1.49      | ~ v2_pre_topc(sK2)
% 7.43/1.49      | ~ l1_pre_topc(X0_54)
% 7.43/1.49      | ~ l1_pre_topc(sK2)
% 7.43/1.49      | ~ v1_funct_1(X0_53) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_880]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2665,plain,
% 7.43/1.49      ( sP1(sK5,sK2,X0_53,sK6,X0_54) = iProver_top
% 7.43/1.49      | r4_tsep_1(sK2,sK5,sK6) != iProver_top
% 7.43/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.43/1.49      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.43/1.49      | m1_pre_topc(sK6,sK2) != iProver_top
% 7.43/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.43/1.49      | v2_struct_0(X0_54) = iProver_top
% 7.43/1.49      | v2_struct_0(sK5) = iProver_top
% 7.43/1.49      | v2_struct_0(sK6) = iProver_top
% 7.43/1.49      | v2_struct_0(sK2) = iProver_top
% 7.43/1.49      | v2_pre_topc(X0_54) != iProver_top
% 7.43/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.43/1.49      | l1_pre_topc(X0_54) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.43/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_2664]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2667,plain,
% 7.43/1.49      ( sP1(sK5,sK2,sK4,sK6,sK3) = iProver_top
% 7.43/1.49      | r4_tsep_1(sK2,sK5,sK6) != iProver_top
% 7.43/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.43/1.49      | m1_pre_topc(sK6,sK2) != iProver_top
% 7.43/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | v2_struct_0(sK5) = iProver_top
% 7.43/1.49      | v2_struct_0(sK6) = iProver_top
% 7.43/1.49      | v2_struct_0(sK3) = iProver_top
% 7.43/1.49      | v2_struct_0(sK2) = iProver_top
% 7.43/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.43/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.43/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_2665]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_906,plain,
% 7.43/1.49      ( ~ l1_pre_topc(X0_54) | l1_struct_0(X0_54) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2731,plain,
% 7.43/1.49      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_906]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2732,plain,
% 7.43/1.49      ( l1_pre_topc(sK2) != iProver_top
% 7.43/1.49      | l1_struct_0(sK2) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_2731]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_44,negated_conjecture,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 7.43/1.49      inference(cnf_transformation,[],[f115]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_875,negated_conjecture,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_44]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1873,plain,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_875]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_110,plain,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_13,plain,
% 7.43/1.49      ( ~ v5_pre_topc(X0,X1,X2)
% 7.43/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.43/1.49      | ~ m1_pre_topc(X3,X1)
% 7.43/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.43/1.49      | v2_struct_0(X1)
% 7.43/1.49      | v2_struct_0(X2)
% 7.43/1.49      | v2_struct_0(X3)
% 7.43/1.49      | ~ v2_pre_topc(X2)
% 7.43/1.49      | ~ v2_pre_topc(X1)
% 7.43/1.49      | ~ l1_pre_topc(X1)
% 7.43/1.49      | ~ l1_pre_topc(X2)
% 7.43/1.49      | ~ v1_funct_1(X0)
% 7.43/1.49      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 7.43/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_895,plain,
% 7.43/1.49      ( ~ v5_pre_topc(X0_53,X0_54,X1_54)
% 7.43/1.49      | ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.43/1.49      | ~ m1_pre_topc(X2_54,X0_54)
% 7.43/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.43/1.49      | v2_struct_0(X1_54)
% 7.43/1.49      | v2_struct_0(X0_54)
% 7.43/1.49      | v2_struct_0(X2_54)
% 7.43/1.49      | ~ v2_pre_topc(X1_54)
% 7.43/1.49      | ~ v2_pre_topc(X0_54)
% 7.43/1.49      | ~ l1_pre_topc(X1_54)
% 7.43/1.49      | ~ l1_pre_topc(X0_54)
% 7.43/1.49      | ~ v1_funct_1(X0_53)
% 7.43/1.49      | v1_funct_1(k2_tmap_1(X0_54,X1_54,X0_53,X2_54)) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_13]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2617,plain,
% 7.43/1.49      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.43/1.49      | ~ m1_pre_topc(X0_54,sK2)
% 7.43/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.43/1.49      | v2_struct_0(X0_54)
% 7.43/1.49      | v2_struct_0(sK3)
% 7.43/1.49      | v2_struct_0(sK2)
% 7.43/1.49      | ~ v2_pre_topc(sK3)
% 7.43/1.49      | ~ v2_pre_topc(sK2)
% 7.43/1.49      | ~ l1_pre_topc(sK3)
% 7.43/1.49      | ~ l1_pre_topc(sK2)
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54))
% 7.43/1.49      | ~ v1_funct_1(sK4) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_895]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2735,plain,
% 7.43/1.49      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.43/1.49      | ~ m1_pre_topc(sK6,sK2)
% 7.43/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.43/1.49      | v2_struct_0(sK6)
% 7.43/1.49      | v2_struct_0(sK3)
% 7.43/1.49      | v2_struct_0(sK2)
% 7.43/1.49      | ~ v2_pre_topc(sK3)
% 7.43/1.49      | ~ v2_pre_topc(sK2)
% 7.43/1.49      | ~ l1_pre_topc(sK3)
% 7.43/1.49      | ~ l1_pre_topc(sK2)
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 7.43/1.49      | ~ v1_funct_1(sK4) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_2617]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2736,plain,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.43/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | m1_pre_topc(sK6,sK2) != iProver_top
% 7.43/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | v2_struct_0(sK6) = iProver_top
% 7.43/1.49      | v2_struct_0(sK3) = iProver_top
% 7.43/1.49      | v2_struct_0(sK2) = iProver_top
% 7.43/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.43/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top
% 7.43/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_2735]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2775,plain,
% 7.43/1.49      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_1873,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,
% 7.43/1.49                 c_89,c_90,c_110,c_2736]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_60,negated_conjecture,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
% 7.43/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_871,negated_conjecture,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_60]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1877,plain,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_871]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_94,plain,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2738,plain,
% 7.43/1.49      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.43/1.49      | ~ m1_pre_topc(sK5,sK2)
% 7.43/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.43/1.49      | v2_struct_0(sK5)
% 7.43/1.49      | v2_struct_0(sK3)
% 7.43/1.49      | v2_struct_0(sK2)
% 7.43/1.49      | ~ v2_pre_topc(sK3)
% 7.43/1.49      | ~ v2_pre_topc(sK2)
% 7.43/1.49      | ~ l1_pre_topc(sK3)
% 7.43/1.49      | ~ l1_pre_topc(sK2)
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.43/1.49      | ~ v1_funct_1(sK4) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_2617]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2739,plain,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.43/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.43/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | v2_struct_0(sK5) = iProver_top
% 7.43/1.49      | v2_struct_0(sK3) = iProver_top
% 7.43/1.49      | v2_struct_0(sK2) = iProver_top
% 7.43/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.43/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top
% 7.43/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_2738]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2905,plain,
% 7.43/1.49      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_1877,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,
% 7.43/1.49                 c_87,c_88,c_94,c_2739]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_36,negated_conjecture,
% 7.43/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.43/1.49      | v5_pre_topc(sK4,sK2,sK3) ),
% 7.43/1.49      inference(cnf_transformation,[],[f123]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_877,negated_conjecture,
% 7.43/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.43/1.49      | v5_pre_topc(sK4,sK2,sK3) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_36]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1871,plain,
% 7.43/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
% 7.43/1.49      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_877]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_118,plain,
% 7.43/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
% 7.43/1.49      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_11,plain,
% 7.43/1.49      ( ~ v5_pre_topc(X0,X1,X2)
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(X1,X2,X0,X3),X3,X2)
% 7.43/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.43/1.49      | ~ m1_pre_topc(X3,X1)
% 7.43/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.43/1.49      | v2_struct_0(X1)
% 7.43/1.49      | v2_struct_0(X2)
% 7.43/1.49      | v2_struct_0(X3)
% 7.43/1.49      | ~ v2_pre_topc(X2)
% 7.43/1.49      | ~ v2_pre_topc(X1)
% 7.43/1.49      | ~ l1_pre_topc(X1)
% 7.43/1.49      | ~ l1_pre_topc(X2)
% 7.43/1.49      | ~ v1_funct_1(X0) ),
% 7.43/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_897,plain,
% 7.43/1.49      ( ~ v5_pre_topc(X0_53,X0_54,X1_54)
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(X0_54,X1_54,X0_53,X2_54),X2_54,X1_54)
% 7.43/1.49      | ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.43/1.49      | ~ m1_pre_topc(X2_54,X0_54)
% 7.43/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.43/1.49      | v2_struct_0(X1_54)
% 7.43/1.49      | v2_struct_0(X0_54)
% 7.43/1.49      | v2_struct_0(X2_54)
% 7.43/1.49      | ~ v2_pre_topc(X1_54)
% 7.43/1.49      | ~ v2_pre_topc(X0_54)
% 7.43/1.49      | ~ l1_pre_topc(X1_54)
% 7.43/1.49      | ~ l1_pre_topc(X0_54)
% 7.43/1.49      | ~ v1_funct_1(X0_53) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_11]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2659,plain,
% 7.43/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_54),X0_54,sK3)
% 7.43/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.43/1.49      | ~ m1_pre_topc(X0_54,sK2)
% 7.43/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.43/1.49      | v2_struct_0(X0_54)
% 7.43/1.49      | v2_struct_0(sK3)
% 7.43/1.49      | v2_struct_0(sK2)
% 7.43/1.49      | ~ v2_pre_topc(sK3)
% 7.43/1.49      | ~ v2_pre_topc(sK2)
% 7.43/1.49      | ~ l1_pre_topc(sK3)
% 7.43/1.49      | ~ l1_pre_topc(sK2)
% 7.43/1.49      | ~ v1_funct_1(sK4) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_897]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2815,plain,
% 7.43/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.43/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.43/1.49      | ~ m1_pre_topc(sK6,sK2)
% 7.43/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.43/1.49      | v2_struct_0(sK6)
% 7.43/1.49      | v2_struct_0(sK3)
% 7.43/1.49      | v2_struct_0(sK2)
% 7.43/1.49      | ~ v2_pre_topc(sK3)
% 7.43/1.49      | ~ v2_pre_topc(sK2)
% 7.43/1.49      | ~ l1_pre_topc(sK3)
% 7.43/1.49      | ~ l1_pre_topc(sK2)
% 7.43/1.49      | ~ v1_funct_1(sK4) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_2659]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2816,plain,
% 7.43/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
% 7.43/1.49      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.43/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | m1_pre_topc(sK6,sK2) != iProver_top
% 7.43/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | v2_struct_0(sK6) = iProver_top
% 7.43/1.49      | v2_struct_0(sK3) = iProver_top
% 7.43/1.49      | v2_struct_0(sK2) = iProver_top
% 7.43/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.43/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.43/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_2815]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2911,plain,
% 7.43/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_1871,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,
% 7.43/1.49                 c_89,c_90,c_118,c_2816]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_52,negated_conjecture,
% 7.43/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.43/1.49      | v5_pre_topc(sK4,sK2,sK3) ),
% 7.43/1.49      inference(cnf_transformation,[],[f107]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_873,negated_conjecture,
% 7.43/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.43/1.49      | v5_pre_topc(sK4,sK2,sK3) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_52]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1875,plain,
% 7.43/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
% 7.43/1.49      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_873]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_102,plain,
% 7.43/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
% 7.43/1.49      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2818,plain,
% 7.43/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.43/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.43/1.49      | ~ m1_pre_topc(sK5,sK2)
% 7.43/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.43/1.49      | v2_struct_0(sK5)
% 7.43/1.49      | v2_struct_0(sK3)
% 7.43/1.49      | v2_struct_0(sK2)
% 7.43/1.49      | ~ v2_pre_topc(sK3)
% 7.43/1.49      | ~ v2_pre_topc(sK2)
% 7.43/1.49      | ~ l1_pre_topc(sK3)
% 7.43/1.49      | ~ l1_pre_topc(sK2)
% 7.43/1.49      | ~ v1_funct_1(sK4) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_2659]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2819,plain,
% 7.43/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
% 7.43/1.49      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.43/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.43/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | v2_struct_0(sK5) = iProver_top
% 7.43/1.49      | v2_struct_0(sK3) = iProver_top
% 7.43/1.49      | v2_struct_0(sK2) = iProver_top
% 7.43/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.43/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.43/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_2818]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3028,plain,
% 7.43/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_1875,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,
% 7.43/1.49                 c_87,c_88,c_102,c_2819]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3,plain,
% 7.43/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.43/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_905,plain,
% 7.43/1.49      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.43/1.49      | ~ l1_pre_topc(X1_54)
% 7.43/1.49      | l1_pre_topc(X0_54) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_868,negated_conjecture,
% 7.43/1.49      ( m1_pre_topc(sK6,sK2) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_65]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3052,plain,
% 7.43/1.49      ( l1_pre_topc(sK6) | ~ l1_pre_topc(sK2) ),
% 7.43/1.49      inference(resolution,[status(thm)],[c_905,c_868]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3057,plain,
% 7.43/1.49      ( l1_pre_topc(sK6) ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_3052,c_75]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3361,plain,
% 7.43/1.49      ( l1_struct_0(sK6) ),
% 7.43/1.49      inference(resolution,[status(thm)],[c_3057,c_906]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3362,plain,
% 7.43/1.49      ( l1_struct_0(sK6) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_3361]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_40,negated_conjecture,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
% 7.43/1.49      inference(cnf_transformation,[],[f119]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_876,negated_conjecture,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_40]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1872,plain,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_876]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_114,plain,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_12,plain,
% 7.43/1.49      ( ~ v5_pre_topc(X0,X1,X2)
% 7.43/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.43/1.49      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 7.43/1.49      | ~ m1_pre_topc(X3,X1)
% 7.43/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.43/1.49      | v2_struct_0(X1)
% 7.43/1.49      | v2_struct_0(X2)
% 7.43/1.49      | v2_struct_0(X3)
% 7.43/1.49      | ~ v2_pre_topc(X2)
% 7.43/1.49      | ~ v2_pre_topc(X1)
% 7.43/1.49      | ~ l1_pre_topc(X1)
% 7.43/1.49      | ~ l1_pre_topc(X2)
% 7.43/1.49      | ~ v1_funct_1(X0) ),
% 7.43/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_896,plain,
% 7.43/1.49      ( ~ v5_pre_topc(X0_53,X0_54,X1_54)
% 7.43/1.49      | ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.43/1.49      | v1_funct_2(k2_tmap_1(X0_54,X1_54,X0_53,X2_54),u1_struct_0(X2_54),u1_struct_0(X1_54))
% 7.43/1.49      | ~ m1_pre_topc(X2_54,X0_54)
% 7.43/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.43/1.49      | v2_struct_0(X1_54)
% 7.43/1.49      | v2_struct_0(X0_54)
% 7.43/1.49      | v2_struct_0(X2_54)
% 7.43/1.49      | ~ v2_pre_topc(X1_54)
% 7.43/1.49      | ~ v2_pre_topc(X0_54)
% 7.43/1.49      | ~ l1_pre_topc(X1_54)
% 7.43/1.49      | ~ l1_pre_topc(X0_54)
% 7.43/1.49      | ~ v1_funct_1(X0_53) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_12]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2654,plain,
% 7.43/1.49      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_54),u1_struct_0(X0_54),u1_struct_0(sK3))
% 7.43/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.43/1.49      | ~ m1_pre_topc(X0_54,sK2)
% 7.43/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.43/1.49      | v2_struct_0(X0_54)
% 7.43/1.49      | v2_struct_0(sK3)
% 7.43/1.49      | v2_struct_0(sK2)
% 7.43/1.49      | ~ v2_pre_topc(sK3)
% 7.43/1.49      | ~ v2_pre_topc(sK2)
% 7.43/1.49      | ~ l1_pre_topc(sK3)
% 7.43/1.49      | ~ l1_pre_topc(sK2)
% 7.43/1.49      | ~ v1_funct_1(sK4) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_896]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2758,plain,
% 7.43/1.49      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.43/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.43/1.49      | ~ m1_pre_topc(sK6,sK2)
% 7.43/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.43/1.49      | v2_struct_0(sK6)
% 7.43/1.49      | v2_struct_0(sK3)
% 7.43/1.49      | v2_struct_0(sK2)
% 7.43/1.49      | ~ v2_pre_topc(sK3)
% 7.43/1.49      | ~ v2_pre_topc(sK2)
% 7.43/1.49      | ~ l1_pre_topc(sK3)
% 7.43/1.49      | ~ l1_pre_topc(sK2)
% 7.43/1.49      | ~ v1_funct_1(sK4) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_2654]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2759,plain,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top
% 7.43/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | m1_pre_topc(sK6,sK2) != iProver_top
% 7.43/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | v2_struct_0(sK6) = iProver_top
% 7.43/1.49      | v2_struct_0(sK3) = iProver_top
% 7.43/1.49      | v2_struct_0(sK2) = iProver_top
% 7.43/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.43/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.43/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_2758]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3390,plain,
% 7.43/1.49      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_1872,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,
% 7.43/1.49                 c_89,c_90,c_114,c_2759]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_56,negated_conjecture,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 7.43/1.49      inference(cnf_transformation,[],[f103]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_872,negated_conjecture,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_56]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1876,plain,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_872]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_98,plain,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2761,plain,
% 7.43/1.49      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.43/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.43/1.49      | ~ m1_pre_topc(sK5,sK2)
% 7.43/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.43/1.49      | v2_struct_0(sK5)
% 7.43/1.49      | v2_struct_0(sK3)
% 7.43/1.49      | v2_struct_0(sK2)
% 7.43/1.49      | ~ v2_pre_topc(sK3)
% 7.43/1.49      | ~ v2_pre_topc(sK2)
% 7.43/1.49      | ~ l1_pre_topc(sK3)
% 7.43/1.49      | ~ l1_pre_topc(sK2)
% 7.43/1.49      | ~ v1_funct_1(sK4) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_2654]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2762,plain,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
% 7.43/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.43/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | v2_struct_0(sK5) = iProver_top
% 7.43/1.49      | v2_struct_0(sK3) = iProver_top
% 7.43/1.49      | v2_struct_0(sK2) = iProver_top
% 7.43/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.43/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.43/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_2761]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3396,plain,
% 7.43/1.49      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_1876,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,
% 7.43/1.49                 c_87,c_88,c_98,c_2762]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_866,negated_conjecture,
% 7.43/1.49      ( m1_pre_topc(sK5,sK2) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_67]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3054,plain,
% 7.43/1.49      ( l1_pre_topc(sK5) | ~ l1_pre_topc(sK2) ),
% 7.43/1.49      inference(resolution,[status(thm)],[c_905,c_866]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3364,plain,
% 7.43/1.49      ( l1_pre_topc(sK5) ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_3054,c_75]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3405,plain,
% 7.43/1.49      ( l1_struct_0(sK5) ),
% 7.43/1.49      inference(resolution,[status(thm)],[c_3364,c_906]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3406,plain,
% 7.43/1.49      ( l1_struct_0(sK5) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_3405]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3127,plain,
% 7.43/1.49      ( sP0(sK3,X0_54,sK4,sK2,sK5)
% 7.43/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_54),X0_54,sK3)
% 7.43/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.43/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_54),u1_struct_0(X0_54),u1_struct_0(sK3))
% 7.43/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.43/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
% 7.43/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.43/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54))
% 7.43/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_889]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4219,plain,
% 7.43/1.49      ( sP0(sK3,sK6,sK4,sK2,sK5)
% 7.43/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.43/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.43/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.43/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.43/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.43/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.43/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.43/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_3127]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4220,plain,
% 7.43/1.49      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_4219]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_8,plain,
% 7.43/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.43/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.43/1.49      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 7.43/1.49      | ~ l1_struct_0(X3)
% 7.43/1.49      | ~ l1_struct_0(X2)
% 7.43/1.49      | ~ l1_struct_0(X1)
% 7.43/1.49      | ~ v1_funct_1(X0) ),
% 7.43/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_900,plain,
% 7.43/1.49      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.43/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.43/1.49      | m1_subset_1(k2_tmap_1(X0_54,X1_54,X0_53,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 7.43/1.49      | ~ l1_struct_0(X2_54)
% 7.43/1.49      | ~ l1_struct_0(X1_54)
% 7.43/1.49      | ~ l1_struct_0(X0_54)
% 7.43/1.49      | ~ v1_funct_1(X0_53) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_8]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2612,plain,
% 7.43/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
% 7.43/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.43/1.49      | ~ l1_struct_0(X0_54)
% 7.43/1.49      | ~ l1_struct_0(sK3)
% 7.43/1.49      | ~ l1_struct_0(sK2)
% 7.43/1.49      | ~ v1_funct_1(sK4) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_900]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4468,plain,
% 7.43/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.43/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.43/1.49      | ~ l1_struct_0(sK5)
% 7.43/1.49      | ~ l1_struct_0(sK3)
% 7.43/1.49      | ~ l1_struct_0(sK2)
% 7.43/1.49      | ~ v1_funct_1(sK4) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_2612]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4469,plain,
% 7.43/1.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top
% 7.43/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | l1_struct_0(sK5) != iProver_top
% 7.43/1.49      | l1_struct_0(sK3) != iProver_top
% 7.43/1.49      | l1_struct_0(sK2) != iProver_top
% 7.43/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_4468]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4537,plain,
% 7.43/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.43/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.43/1.49      | ~ l1_struct_0(sK6)
% 7.43/1.49      | ~ l1_struct_0(sK3)
% 7.43/1.49      | ~ l1_struct_0(sK2)
% 7.43/1.49      | ~ v1_funct_1(sK4) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_2612]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4538,plain,
% 7.43/1.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top
% 7.43/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | l1_struct_0(sK6) != iProver_top
% 7.43/1.49      | l1_struct_0(sK3) != iProver_top
% 7.43/1.49      | l1_struct_0(sK2) != iProver_top
% 7.43/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_4537]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4858,plain,
% 7.43/1.49      ( sP1(sK5,sK2,sK4,sK6,sK3) != iProver_top
% 7.43/1.49      | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_4856]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3195,plain,
% 7.43/1.49      ( sP0(sK3,X0_54,sK4,sK2,sK6)
% 7.43/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_54),X0_54,sK3)
% 7.43/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.43/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_54),u1_struct_0(X0_54),u1_struct_0(sK3))
% 7.43/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.43/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
% 7.43/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.43/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54))
% 7.43/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_889]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_5050,plain,
% 7.43/1.49      ( sP0(sK3,sK2,sK4,sK2,sK6)
% 7.43/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.43/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3)
% 7.43/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.43/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
% 7.43/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.43/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.43/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 7.43/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_3195]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_5056,plain,
% 7.43/1.49      ( sP0(sK3,sK2,sK4,sK2,sK6) = iProver_top
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_5050]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_5844,plain,
% 7.43/1.49      ( sP1(sK5,sK2,sK4,sK6,sK3) != iProver_top
% 7.43/1.49      | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_5841]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6010,plain,
% 7.43/1.49      ( sP1(sK5,sK2,sK4,sK6,sK3) != iProver_top
% 7.43/1.49      | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_6007]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_7217,plain,
% 7.43/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.43/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.43/1.49      | ~ l1_struct_0(sK3)
% 7.43/1.49      | ~ l1_struct_0(sK2)
% 7.43/1.49      | ~ v1_funct_1(sK4) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_2612]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_7218,plain,
% 7.43/1.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top
% 7.43/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | l1_struct_0(sK3) != iProver_top
% 7.43/1.49      | l1_struct_0(sK2) != iProver_top
% 7.43/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_7217]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_13543,plain,
% 7.43/1.49      ( sP0(sK3,sK2,sK4,sK2,sK6) = iProver_top ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_13357,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,
% 7.43/1.49                 c_87,c_88,c_89,c_90,c_91,c_94,c_98,c_102,c_110,c_114,
% 7.43/1.49                 c_118,c_198,c_2667,c_2732,c_2736,c_2739,c_2759,c_2762,
% 7.43/1.49                 c_2816,c_2819,c_3362,c_3406,c_4220,c_4469,c_4538,c_4858,
% 7.43/1.49                 c_5056,c_5844,c_6010,c_7218]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_20,plain,
% 7.43/1.49      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.43/1.49      | m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
% 7.43/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_888,plain,
% 7.43/1.49      ( ~ sP0(X0_54,X1_54,X0_53,X2_54,X3_54)
% 7.43/1.49      | m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_53,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_20]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1860,plain,
% 7.43/1.49      ( sP0(X0_54,X1_54,X0_53,X2_54,X3_54) != iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_53,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_888]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_13549,plain,
% 7.43/1.49      ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_13543,c_1860]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_864,negated_conjecture,
% 7.43/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_69]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1883,plain,
% 7.43/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_864]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1,plain,
% 7.43/1.49      ( ~ r2_funct_2(X0,X1,X2,X3)
% 7.43/1.49      | ~ v1_funct_2(X3,X0,X1)
% 7.43/1.49      | ~ v1_funct_2(X2,X0,X1)
% 7.43/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.43/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.43/1.49      | ~ v1_funct_1(X3)
% 7.43/1.49      | ~ v1_funct_1(X2)
% 7.43/1.49      | X2 = X3 ),
% 7.43/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_907,plain,
% 7.43/1.49      ( ~ r2_funct_2(X0_55,X1_55,X0_53,X1_53)
% 7.43/1.49      | ~ v1_funct_2(X1_53,X0_55,X1_55)
% 7.43/1.49      | ~ v1_funct_2(X0_53,X0_55,X1_55)
% 7.43/1.49      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 7.43/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 7.43/1.49      | ~ v1_funct_1(X0_53)
% 7.43/1.49      | ~ v1_funct_1(X1_53)
% 7.43/1.49      | X0_53 = X1_53 ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1841,plain,
% 7.43/1.49      ( X0_53 = X1_53
% 7.43/1.49      | r2_funct_2(X0_55,X1_55,X0_53,X1_53) != iProver_top
% 7.43/1.49      | v1_funct_2(X0_53,X0_55,X1_55) != iProver_top
% 7.43/1.49      | v1_funct_2(X1_53,X0_55,X1_55) != iProver_top
% 7.43/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 7.43/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 7.43/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.43/1.49      | v1_funct_1(X1_53) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_907]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3042,plain,
% 7.43/1.49      ( sK4 = X0_53
% 7.43/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_53) != iProver_top
% 7.43/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.43/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_1883,c_1841]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4240,plain,
% 7.43/1.49      ( v1_funct_1(X0_53) != iProver_top
% 7.43/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | sK4 = X0_53
% 7.43/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_53) != iProver_top
% 7.43/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_3042,c_84,c_85]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4241,plain,
% 7.43/1.49      ( sK4 = X0_53
% 7.43/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_53) != iProver_top
% 7.43/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.43/1.49      inference(renaming,[status(thm)],[c_4240]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_14892,plain,
% 7.43/1.49      ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4
% 7.43/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_13549,c_4241]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_916,plain,
% 7.43/1.49      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 7.43/1.49      theory(equality) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_911,plain,( X0_54 = X0_54 ),theory(equality) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3837,plain,
% 7.43/1.49      ( X0_54 != X1_54 | X1_54 = X0_54 ),
% 7.43/1.49      inference(resolution,[status(thm)],[c_916,c_911]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4568,plain,
% 7.43/1.49      ( sK2 = k1_tsep_1(sK2,sK5,sK6) ),
% 7.43/1.49      inference(resolution,[status(thm)],[c_3837,c_869]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_924,plain,
% 7.43/1.49      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.43/1.49      | m1_pre_topc(X2_54,X3_54)
% 7.43/1.49      | X2_54 != X0_54
% 7.43/1.49      | X3_54 != X1_54 ),
% 7.43/1.49      theory(equality) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4749,plain,
% 7.43/1.49      ( ~ m1_pre_topc(X0_54,k1_tsep_1(sK2,sK5,sK6))
% 7.43/1.49      | m1_pre_topc(X1_54,sK2)
% 7.43/1.49      | X1_54 != X0_54 ),
% 7.43/1.49      inference(resolution,[status(thm)],[c_4568,c_924]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3993,plain,
% 7.43/1.49      ( m1_pre_topc(X0_54,k1_tsep_1(sK2,sK5,sK6))
% 7.43/1.49      | ~ m1_pre_topc(X1_54,sK2)
% 7.43/1.49      | X0_54 != X1_54 ),
% 7.43/1.49      inference(resolution,[status(thm)],[c_924,c_869]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4167,plain,
% 7.43/1.49      ( m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),k1_tsep_1(sK2,sK5,sK6))
% 7.43/1.49      | ~ m1_pre_topc(sK2,sK2) ),
% 7.43/1.49      inference(resolution,[status(thm)],[c_3993,c_869]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6,plain,
% 7.43/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.43/1.49      | ~ m1_pre_topc(X2,X1)
% 7.43/1.49      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 7.43/1.49      | v2_struct_0(X1)
% 7.43/1.49      | v2_struct_0(X0)
% 7.43/1.49      | v2_struct_0(X2)
% 7.43/1.49      | ~ l1_pre_topc(X1) ),
% 7.43/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_902,plain,
% 7.43/1.49      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.43/1.49      | ~ m1_pre_topc(X2_54,X1_54)
% 7.43/1.49      | m1_pre_topc(k1_tsep_1(X1_54,X0_54,X2_54),X1_54)
% 7.43/1.49      | v2_struct_0(X1_54)
% 7.43/1.49      | v2_struct_0(X0_54)
% 7.43/1.49      | v2_struct_0(X2_54)
% 7.43/1.49      | ~ l1_pre_topc(X1_54) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2573,plain,
% 7.43/1.49      ( ~ m1_pre_topc(X0_54,sK2)
% 7.43/1.49      | m1_pre_topc(k1_tsep_1(sK2,X0_54,sK6),sK2)
% 7.43/1.49      | ~ m1_pre_topc(sK6,sK2)
% 7.43/1.49      | v2_struct_0(X0_54)
% 7.43/1.49      | v2_struct_0(sK6)
% 7.43/1.49      | v2_struct_0(sK2)
% 7.43/1.49      | ~ l1_pre_topc(sK2) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_902]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2722,plain,
% 7.43/1.49      ( m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2)
% 7.43/1.49      | ~ m1_pre_topc(sK5,sK2)
% 7.43/1.49      | ~ m1_pre_topc(sK6,sK2)
% 7.43/1.49      | v2_struct_0(sK5)
% 7.43/1.49      | v2_struct_0(sK6)
% 7.43/1.49      | v2_struct_0(sK2)
% 7.43/1.49      | ~ l1_pre_topc(sK2) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_2573]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2876,plain,
% 7.43/1.49      ( m1_pre_topc(X0_54,X1_54)
% 7.43/1.49      | ~ m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2)
% 7.43/1.49      | X0_54 != k1_tsep_1(sK2,sK5,sK6)
% 7.43/1.49      | X1_54 != sK2 ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_924]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3620,plain,
% 7.43/1.49      ( m1_pre_topc(X0_54,k1_tsep_1(sK2,sK5,sK6))
% 7.43/1.49      | ~ m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2)
% 7.43/1.49      | X0_54 != k1_tsep_1(sK2,sK5,sK6)
% 7.43/1.49      | k1_tsep_1(sK2,sK5,sK6) != sK2 ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_2876]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3863,plain,
% 7.43/1.49      ( m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),k1_tsep_1(sK2,sK5,sK6))
% 7.43/1.49      | ~ m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),sK2)
% 7.43/1.49      | k1_tsep_1(sK2,sK5,sK6) != k1_tsep_1(sK2,sK5,sK6)
% 7.43/1.49      | k1_tsep_1(sK2,sK5,sK6) != sK2 ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_3620]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3864,plain,
% 7.43/1.49      ( k1_tsep_1(sK2,sK5,sK6) = k1_tsep_1(sK2,sK5,sK6) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_911]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4178,plain,
% 7.43/1.49      ( m1_pre_topc(k1_tsep_1(sK2,sK5,sK6),k1_tsep_1(sK2,sK5,sK6)) ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_4167,c_77,c_75,c_68,c_67,c_66,c_65,c_869,c_2722,
% 7.43/1.49                 c_3863,c_3864]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_5299,plain,
% 7.43/1.49      ( m1_pre_topc(X0_54,sK2) | X0_54 != k1_tsep_1(sK2,sK5,sK6) ),
% 7.43/1.49      inference(resolution,[status(thm)],[c_4749,c_4178]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_5321,plain,
% 7.43/1.49      ( m1_pre_topc(sK2,sK2) ),
% 7.43/1.49      inference(resolution,[status(thm)],[c_5299,c_4568]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_5322,plain,
% 7.43/1.49      ( m1_pre_topc(sK2,sK2) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_5321]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_8263,plain,
% 7.43/1.49      ( k2_tmap_1(sK2,sK3,X0_53,sK2) = sK4
% 7.43/1.49      | sP1(sK5,sK2,X0_53,sK6,sK3) != iProver_top
% 7.43/1.49      | sP0(sK3,sK6,X0_53,sK2,sK5) != iProver_top
% 7.43/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,X0_53,sK2)) != iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,X0_53,sK2)) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_7927,c_4241]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_8730,plain,
% 7.43/1.49      ( k2_tmap_1(sK2,sK3,X0_53,sK2) = sK4
% 7.43/1.49      | sP1(sK5,sK2,X0_53,sK6,sK3) != iProver_top
% 7.43/1.49      | sP0(sK3,sK6,X0_53,sK2,sK5) != iProver_top
% 7.43/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,X0_53,sK2)) != iProver_top ),
% 7.43/1.49      inference(forward_subsumption_resolution,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_8263,c_4856,c_6007]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_8732,plain,
% 7.43/1.49      ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4
% 7.43/1.49      | sP1(sK5,sK2,sK4,sK6,sK3) != iProver_top
% 7.43/1.49      | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.43/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_8730]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1846,plain,
% 7.43/1.49      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.43/1.49      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 7.43/1.49      | m1_pre_topc(k1_tsep_1(X1_54,X0_54,X2_54),X1_54) = iProver_top
% 7.43/1.49      | v2_struct_0(X1_54) = iProver_top
% 7.43/1.49      | v2_struct_0(X0_54) = iProver_top
% 7.43/1.49      | v2_struct_0(X2_54) = iProver_top
% 7.43/1.49      | l1_pre_topc(X1_54) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_902]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_5512,plain,
% 7.43/1.49      ( m1_pre_topc(sK5,sK2) != iProver_top
% 7.43/1.49      | m1_pre_topc(sK6,sK2) != iProver_top
% 7.43/1.49      | m1_pre_topc(sK2,sK2) = iProver_top
% 7.43/1.49      | v2_struct_0(sK5) = iProver_top
% 7.43/1.49      | v2_struct_0(sK6) = iProver_top
% 7.43/1.49      | v2_struct_0(sK2) = iProver_top
% 7.43/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_869,c_1846]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6308,plain,
% 7.43/1.49      ( m1_pre_topc(sK2,sK2) = iProver_top ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_5512,c_5322]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_5,plain,
% 7.43/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.43/1.49      | ~ m1_pre_topc(X3,X4)
% 7.43/1.49      | ~ m1_pre_topc(X3,X1)
% 7.43/1.49      | ~ m1_pre_topc(X1,X4)
% 7.43/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.43/1.49      | v2_struct_0(X4)
% 7.43/1.49      | v2_struct_0(X2)
% 7.43/1.49      | ~ v2_pre_topc(X2)
% 7.43/1.49      | ~ v2_pre_topc(X4)
% 7.43/1.49      | ~ l1_pre_topc(X4)
% 7.43/1.49      | ~ l1_pre_topc(X2)
% 7.43/1.49      | ~ v1_funct_1(X0)
% 7.43/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 7.43/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_903,plain,
% 7.43/1.49      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.43/1.49      | ~ m1_pre_topc(X0_54,X2_54)
% 7.43/1.49      | ~ m1_pre_topc(X3_54,X0_54)
% 7.43/1.49      | ~ m1_pre_topc(X3_54,X2_54)
% 7.43/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.43/1.49      | v2_struct_0(X2_54)
% 7.43/1.49      | v2_struct_0(X1_54)
% 7.43/1.49      | ~ v2_pre_topc(X1_54)
% 7.43/1.49      | ~ v2_pre_topc(X2_54)
% 7.43/1.49      | ~ l1_pre_topc(X2_54)
% 7.43/1.49      | ~ l1_pre_topc(X1_54)
% 7.43/1.49      | ~ v1_funct_1(X0_53)
% 7.43/1.49      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_53,u1_struct_0(X3_54)) = k3_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1845,plain,
% 7.43/1.49      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_53,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_53)
% 7.43/1.49      | v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.43/1.49      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 7.43/1.49      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 7.43/1.49      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 7.43/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.43/1.49      | v2_struct_0(X1_54) = iProver_top
% 7.43/1.49      | v2_struct_0(X3_54) = iProver_top
% 7.43/1.49      | v2_pre_topc(X1_54) != iProver_top
% 7.43/1.49      | v2_pre_topc(X3_54) != iProver_top
% 7.43/1.49      | l1_pre_topc(X1_54) != iProver_top
% 7.43/1.49      | l1_pre_topc(X3_54) != iProver_top
% 7.43/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_903]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4651,plain,
% 7.43/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK3,sK2,X0_54,sK4)
% 7.43/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.43/1.49      | m1_pre_topc(X0_54,sK2) != iProver_top
% 7.43/1.49      | m1_pre_topc(sK2,X1_54) != iProver_top
% 7.43/1.49      | v2_struct_0(X1_54) = iProver_top
% 7.43/1.49      | v2_struct_0(sK3) = iProver_top
% 7.43/1.49      | v2_pre_topc(X1_54) != iProver_top
% 7.43/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.43/1.49      | l1_pre_topc(X1_54) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.43/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_1883,c_1845]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_5164,plain,
% 7.43/1.49      ( v2_pre_topc(X1_54) != iProver_top
% 7.43/1.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK3,sK2,X0_54,sK4)
% 7.43/1.49      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.43/1.49      | m1_pre_topc(X0_54,sK2) != iProver_top
% 7.43/1.49      | m1_pre_topc(sK2,X1_54) != iProver_top
% 7.43/1.49      | v2_struct_0(X1_54) = iProver_top
% 7.43/1.49      | l1_pre_topc(X1_54) != iProver_top ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_4651,c_81,c_82,c_83,c_84,c_85]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_5165,plain,
% 7.43/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK3,sK2,X0_54,sK4)
% 7.43/1.49      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.43/1.49      | m1_pre_topc(X0_54,sK2) != iProver_top
% 7.43/1.49      | m1_pre_topc(sK2,X1_54) != iProver_top
% 7.43/1.49      | v2_struct_0(X1_54) = iProver_top
% 7.43/1.49      | v2_pre_topc(X1_54) != iProver_top
% 7.43/1.49      | l1_pre_topc(X1_54) != iProver_top ),
% 7.43/1.49      inference(renaming,[status(thm)],[c_5164]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6314,plain,
% 7.43/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK2,sK3,sK2,sK2,sK4)
% 7.43/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.43/1.49      | v2_struct_0(sK2) = iProver_top
% 7.43/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_6308,c_5165]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4,plain,
% 7.43/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.43/1.49      | ~ m1_pre_topc(X3,X1)
% 7.43/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.43/1.49      | v2_struct_0(X1)
% 7.43/1.49      | v2_struct_0(X2)
% 7.43/1.49      | ~ v2_pre_topc(X2)
% 7.43/1.49      | ~ v2_pre_topc(X1)
% 7.43/1.49      | ~ l1_pre_topc(X1)
% 7.43/1.49      | ~ l1_pre_topc(X2)
% 7.43/1.49      | ~ v1_funct_1(X0)
% 7.43/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 7.43/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_904,plain,
% 7.43/1.49      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.43/1.49      | ~ m1_pre_topc(X2_54,X0_54)
% 7.43/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.43/1.49      | v2_struct_0(X1_54)
% 7.43/1.49      | v2_struct_0(X0_54)
% 7.43/1.49      | ~ v2_pre_topc(X1_54)
% 7.43/1.49      | ~ v2_pre_topc(X0_54)
% 7.43/1.49      | ~ l1_pre_topc(X1_54)
% 7.43/1.49      | ~ l1_pre_topc(X0_54)
% 7.43/1.49      | ~ v1_funct_1(X0_53)
% 7.43/1.49      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_53,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_53,X2_54) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1844,plain,
% 7.43/1.49      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_53,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_53,X2_54)
% 7.43/1.49      | v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.43/1.49      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 7.43/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.43/1.49      | v2_struct_0(X1_54) = iProver_top
% 7.43/1.49      | v2_struct_0(X0_54) = iProver_top
% 7.43/1.49      | v2_pre_topc(X1_54) != iProver_top
% 7.43/1.49      | v2_pre_topc(X0_54) != iProver_top
% 7.43/1.49      | l1_pre_topc(X1_54) != iProver_top
% 7.43/1.49      | l1_pre_topc(X0_54) != iProver_top
% 7.43/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_904]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3747,plain,
% 7.43/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK3,sK4,X0_54)
% 7.43/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | m1_pre_topc(X0_54,sK2) != iProver_top
% 7.43/1.49      | v2_struct_0(sK3) = iProver_top
% 7.43/1.49      | v2_struct_0(sK2) = iProver_top
% 7.43/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.43/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.43/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_1883,c_1844]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4478,plain,
% 7.43/1.49      ( m1_pre_topc(X0_54,sK2) != iProver_top
% 7.43/1.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK3,sK4,X0_54) ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_3747,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4479,plain,
% 7.43/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK3,sK4,X0_54)
% 7.43/1.49      | m1_pre_topc(X0_54,sK2) != iProver_top ),
% 7.43/1.49      inference(renaming,[status(thm)],[c_4478]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6316,plain,
% 7.43/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK3,sK4,sK2) ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_6308,c_4479]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6319,plain,
% 7.43/1.49      ( k3_tmap_1(sK2,sK3,sK2,sK2,sK4) = k2_tmap_1(sK2,sK3,sK4,sK2)
% 7.43/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.43/1.49      | v2_struct_0(sK2) = iProver_top
% 7.43/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.43/1.49      inference(light_normalisation,[status(thm)],[c_6314,c_6316]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6325,plain,
% 7.43/1.49      ( k3_tmap_1(sK2,sK3,sK2,sK2,sK4) = k2_tmap_1(sK2,sK3,sK4,sK2)
% 7.43/1.49      | v2_struct_0(sK2) = iProver_top
% 7.43/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.43/1.49      inference(forward_subsumption_resolution,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_6319,c_6308]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6694,plain,
% 7.43/1.49      ( k3_tmap_1(sK2,sK3,sK2,sK2,sK4) = k2_tmap_1(sK2,sK3,sK4,sK2) ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_6325,c_78,c_79,c_80]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_29,plain,
% 7.43/1.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
% 7.43/1.49      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 7.43/1.49      | ~ m1_pre_topc(X0,X3)
% 7.43/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.43/1.49      | v2_struct_0(X3)
% 7.43/1.49      | v2_struct_0(X1)
% 7.43/1.49      | v2_struct_0(X0)
% 7.43/1.49      | ~ v2_pre_topc(X1)
% 7.43/1.49      | ~ v2_pre_topc(X3)
% 7.43/1.49      | ~ l1_pre_topc(X3)
% 7.43/1.49      | ~ l1_pre_topc(X1)
% 7.43/1.49      | ~ v1_funct_1(X2) ),
% 7.43/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_879,plain,
% 7.43/1.49      ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_53,k3_tmap_1(X2_54,X1_54,X0_54,X0_54,X0_53))
% 7.43/1.49      | ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.43/1.49      | ~ m1_pre_topc(X0_54,X2_54)
% 7.43/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.43/1.49      | v2_struct_0(X1_54)
% 7.43/1.49      | v2_struct_0(X0_54)
% 7.43/1.49      | v2_struct_0(X2_54)
% 7.43/1.49      | ~ v2_pre_topc(X1_54)
% 7.43/1.49      | ~ v2_pre_topc(X2_54)
% 7.43/1.49      | ~ l1_pre_topc(X1_54)
% 7.43/1.49      | ~ l1_pre_topc(X2_54)
% 7.43/1.49      | ~ v1_funct_1(X0_53) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_29]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1869,plain,
% 7.43/1.49      ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_53,k3_tmap_1(X2_54,X1_54,X0_54,X0_54,X0_53)) = iProver_top
% 7.43/1.49      | v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.43/1.49      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 7.43/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.43/1.49      | v2_struct_0(X1_54) = iProver_top
% 7.43/1.49      | v2_struct_0(X0_54) = iProver_top
% 7.43/1.49      | v2_struct_0(X2_54) = iProver_top
% 7.43/1.49      | v2_pre_topc(X1_54) != iProver_top
% 7.43/1.49      | v2_pre_topc(X2_54) != iProver_top
% 7.43/1.49      | l1_pre_topc(X1_54) != iProver_top
% 7.43/1.49      | l1_pre_topc(X2_54) != iProver_top
% 7.43/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_879]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_9329,plain,
% 7.43/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top
% 7.43/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.43/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | v2_struct_0(sK3) = iProver_top
% 7.43/1.49      | v2_struct_0(sK2) = iProver_top
% 7.43/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.43/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.43/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.43/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_6694,c_1869]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_15737,plain,
% 7.43/1.49      ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4 ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_14892,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,
% 7.43/1.49                 c_87,c_88,c_89,c_90,c_91,c_94,c_98,c_102,c_110,c_114,
% 7.43/1.49                 c_118,c_198,c_2667,c_2732,c_2736,c_2739,c_2759,c_2762,
% 7.43/1.49                 c_2816,c_2819,c_3362,c_3406,c_4220,c_4469,c_4538,c_5322,
% 7.43/1.49                 c_8732,c_9329]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_21,plain,
% 7.43/1.49      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) ),
% 7.43/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_887,plain,
% 7.43/1.49      ( ~ sP0(X0_54,X1_54,X0_53,X2_54,X3_54)
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_53,X1_54),X1_54,X0_54) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_21]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1861,plain,
% 7.43/1.49      ( sP0(X0_54,X1_54,X0_53,X2_54,X3_54) != iProver_top
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_53,X1_54),X1_54,X0_54) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_887]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_13553,plain,
% 7.43/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_13543,c_1861]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_15743,plain,
% 7.43/1.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.43/1.49      inference(demodulation,[status(thm)],[c_15737,c_13553]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_30,negated_conjecture,
% 7.43/1.49      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.43/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.43/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.43/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.43/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.43/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.43/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.43/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.43/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.43/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 7.43/1.49      | ~ v1_funct_1(sK4) ),
% 7.43/1.49      inference(cnf_transformation,[],[f129]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_582,plain,
% 7.43/1.49      ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 7.43/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.43/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.43/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.43/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.43/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.43/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.43/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_30,c_71,c_70,c_69]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_583,negated_conjecture,
% 7.43/1.49      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.43/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.43/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.43/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.43/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.43/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.43/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.43/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 7.43/1.49      inference(renaming,[status(thm)],[c_582]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_855,negated_conjecture,
% 7.43/1.49      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.43/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.43/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.43/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.43/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.43/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.43/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.43/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.43/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 7.43/1.49      inference(subtyping,[status(esa)],[c_583]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1892,plain,
% 7.43/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.43/1.49      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_855]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_584,plain,
% 7.43/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.43/1.49      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 7.43/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2765,plain,
% 7.43/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.43/1.49      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.43/1.49      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.43/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_1892,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,
% 7.43/1.49                 c_87,c_88,c_89,c_90,c_94,c_98,c_110,c_114,c_584,c_2736,
% 7.43/1.49                 c_2739,c_2759,c_2762]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(contradiction,plain,
% 7.43/1.49      ( $false ),
% 7.43/1.49      inference(minisat,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_15743,c_4538,c_4469,c_3406,c_3362,c_3028,c_2911,
% 7.43/1.49                 c_2765,c_2732,c_198,c_86,c_85,c_84,c_83,c_80]) ).
% 7.43/1.49  
% 7.43/1.49  
% 7.43/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.43/1.49  
% 7.43/1.49  ------                               Statistics
% 7.43/1.49  
% 7.43/1.49  ------ Selected
% 7.43/1.49  
% 7.43/1.49  total_time:                             0.632
% 7.43/1.49  
%------------------------------------------------------------------------------
