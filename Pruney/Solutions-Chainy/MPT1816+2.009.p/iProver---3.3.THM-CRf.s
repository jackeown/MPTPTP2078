%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:20 EST 2020

% Result     : Theorem 7.89s
% Output     : CNFRefutation 7.89s
% Verified   : 
% Statistics : Number of formulae       :  308 (3699 expanded)
%              Number of clauses        :  220 ( 663 expanded)
%              Number of leaves         :   26 (1374 expanded)
%              Depth                    :   21
%              Number of atoms          : 2325 (125765 expanded)
%              Number of equality atoms :  499 (4355 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal clause size      :   78 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f80,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f91,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f52])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f57,plain,(
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

fof(f83,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f89,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f90,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f52])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f58,plain,(
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

fof(f96,plain,(
    k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f52])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(flattening,[],[f29])).

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
    inference(cnf_transformation,[],[f30])).

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

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

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
    inference(definition_folding,[],[f27,f36,f35])).

fof(f79,plain,(
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

fof(f97,plain,(
    r4_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f92,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f93,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f94,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f95,plain,(
    m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f52])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f38,plain,(
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

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f78,plain,(
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

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f124,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

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

fof(f24,plain,(
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
    inference(flattening,[],[f24])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f100,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f116,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f130,plain,
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

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f120,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f108,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f104,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_27,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2529,plain,
    ( m1_pre_topc(X0_53,X0_53)
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_3599,plain,
    ( m1_pre_topc(X0_53,X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2529])).

cnf(c_69,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2513,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_69])).

cnf(c_3614,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2513])).

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
    inference(cnf_transformation,[],[f57])).

cnf(c_2546,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X2_53,X0_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(X1_53)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(X1_53)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,X0_54,X2_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3582,plain,
    ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,X0_54,X2_53)
    | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2546])).

cnf(c_4579,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k2_tmap_1(sK2,sK3,sK4,X0_53)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_53,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3614,c_3582])).

cnf(c_77,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_78,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_77])).

cnf(c_76,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_79,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_76])).

cnf(c_75,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_80,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_75])).

cnf(c_74,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_81,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_74])).

cnf(c_73,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_82,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_72,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_83,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_72])).

cnf(c_71,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_84,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_70,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_85,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_70])).

cnf(c_7896,plain,
    ( m1_pre_topc(X0_53,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k2_tmap_1(sK2,sK3,sK4,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4579,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85])).

cnf(c_7897,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k2_tmap_1(sK2,sK3,sK4,X0_53)
    | m1_pre_topc(X0_53,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_7896])).

cnf(c_7904,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK3,sK4,sK2)
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3599,c_7897])).

cnf(c_3999,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2529])).

cnf(c_3876,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_53,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k2_tmap_1(sK2,sK3,sK4,X0_53) ),
    inference(instantiation,[status(thm)],[c_2546])).

cnf(c_4419,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK3,sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_3876])).

cnf(c_8150,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK3,sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7904,c_77,c_76,c_75,c_74,c_73,c_72,c_71,c_70,c_69,c_3999,c_4419])).

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
    inference(cnf_transformation,[],[f58])).

cnf(c_2545,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X2_53,X0_53)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ m1_pre_topc(X2_53,X3_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | v2_struct_0(X3_53)
    | v2_struct_0(X1_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X3_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X3_53)
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3583,plain,
    ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_54)
    | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | m1_pre_topc(X2_53,X3_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X3_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2545])).

cnf(c_4791,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK3,sK2,X0_53,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3614,c_3583])).

cnf(c_8054,plain,
    ( v2_pre_topc(X1_53) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK3,sK2,X0_53,sK4)
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4791,c_81,c_82,c_83,c_84,c_85])).

cnf(c_8055,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK3,sK2,X0_53,sK4)
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_8054])).

cnf(c_8062,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X0_53,sK3,sK2,X0_53,sK4)
    | m1_pre_topc(X0_53,sK2) != iProver_top
    | m1_pre_topc(sK2,X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_3599,c_8055])).

cnf(c_2565,plain,
    ( ~ l1_pre_topc(X0_53)
    | l1_pre_topc(X1_53)
    | X1_53 != X0_53 ),
    theory(equality)).

cnf(c_64,negated_conjecture,
    ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2518,negated_conjecture,
    ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(subtyping,[status(esa)],[c_64])).

cnf(c_4532,plain,
    ( l1_pre_topc(k1_tsep_1(sK2,sK5,sK6))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_2565,c_2518])).

cnf(c_4533,plain,
    ( l1_pre_topc(k1_tsep_1(sK2,sK5,sK6)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4532])).

cnf(c_2566,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | m1_pre_topc(X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_5092,plain,
    ( m1_pre_topc(X0_53,k1_tsep_1(sK2,sK5,sK6))
    | ~ m1_pre_topc(X1_53,sK2)
    | X0_53 != X1_53 ),
    inference(resolution,[status(thm)],[c_2566,c_2518])).

cnf(c_2552,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_5236,plain,
    ( m1_pre_topc(X0_53,k1_tsep_1(sK2,sK5,sK6))
    | ~ m1_pre_topc(X0_53,sK2) ),
    inference(resolution,[status(thm)],[c_5092,c_2552])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2547,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_5293,plain,
    ( ~ m1_pre_topc(X0_53,sK2)
    | l1_pre_topc(X0_53)
    | ~ l1_pre_topc(k1_tsep_1(sK2,sK5,sK6)) ),
    inference(resolution,[status(thm)],[c_5236,c_2547])).

cnf(c_5294,plain,
    ( m1_pre_topc(X0_53,sK2) != iProver_top
    | l1_pre_topc(X0_53) = iProver_top
    | l1_pre_topc(k1_tsep_1(sK2,sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5293])).

cnf(c_8455,plain,
    ( v2_pre_topc(X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | m1_pre_topc(sK2,X0_53) != iProver_top
    | m1_pre_topc(X0_53,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X0_53,sK3,sK2,X0_53,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8062,c_80,c_4533,c_5294])).

cnf(c_8456,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X0_53,sK3,sK2,X0_53,sK4)
    | m1_pre_topc(X0_53,sK2) != iProver_top
    | m1_pre_topc(sK2,X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_8455])).

cnf(c_8463,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK2,sK3,sK2,sK2,sK4)
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3599,c_8456])).

cnf(c_3916,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_53,X1_53)
    | ~ m1_pre_topc(X0_53,sK2)
    | ~ m1_pre_topc(sK2,X1_53)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(X1_53)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK3,sK2,X0_53,sK4) ),
    inference(instantiation,[status(thm)],[c_2545])).

cnf(c_4430,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_53,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k3_tmap_1(sK2,sK3,sK2,X0_53,sK4) ),
    inference(instantiation,[status(thm)],[c_3916])).

cnf(c_5006,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK2,sK3,sK2,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_4430])).

cnf(c_8639,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK2,sK3,sK2,sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8463,c_77,c_76,c_75,c_74,c_73,c_72,c_71,c_70,c_69,c_3999,c_5006])).

cnf(c_8641,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK2,sK4) = k2_tmap_1(sK2,sK3,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_8150,c_8639])).

cnf(c_28,plain,
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

cnf(c_2528,plain,
    ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,k3_tmap_1(X2_53,X1_53,X0_53,X0_53,X0_54))
    | ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_3600,plain,
    ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,k3_tmap_1(X2_53,X1_53,X0_53,X0_53,X0_54)) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2528])).

cnf(c_23907,plain,
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
    inference(superposition,[status(thm)],[c_8641,c_3600])).

cnf(c_2558,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_8564,plain,
    ( X0_54 != X1_54
    | X0_54 = k2_tmap_1(sK2,X0_53,X2_54,sK2)
    | k2_tmap_1(sK2,X0_53,X2_54,sK2) != X1_54 ),
    inference(instantiation,[status(thm)],[c_2558])).

cnf(c_8565,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK2) != sK4
    | sK4 = k2_tmap_1(sK2,sK3,sK4,sK2)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_8564])).

cnf(c_2572,plain,
    ( ~ v5_pre_topc(X0_54,X0_53,X1_53)
    | v5_pre_topc(X1_54,X2_53,X3_53)
    | X1_54 != X0_54
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_4310,plain,
    ( v5_pre_topc(X0_54,X0_53,X1_53)
    | ~ v5_pre_topc(X1_54,k1_tsep_1(sK2,sK5,sK6),X2_53)
    | X0_54 != X1_54
    | X1_53 != X2_53
    | X0_53 != k1_tsep_1(sK2,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_2572])).

cnf(c_7202,plain,
    ( ~ v5_pre_topc(X0_54,k1_tsep_1(sK2,sK5,sK6),X0_53)
    | v5_pre_topc(X1_54,sK2,X1_53)
    | X1_54 != X0_54
    | X1_53 != X0_53
    | sK2 != k1_tsep_1(sK2,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_4310])).

cnf(c_8548,plain,
    ( v5_pre_topc(X0_54,sK2,X0_53)
    | ~ v5_pre_topc(k2_tmap_1(sK2,X1_53,X1_54,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X1_53)
    | X0_54 != k2_tmap_1(sK2,X1_53,X1_54,k1_tsep_1(sK2,sK5,sK6))
    | X0_53 != X1_53
    | sK2 != k1_tsep_1(sK2,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_7202])).

cnf(c_8550,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | v5_pre_topc(sK4,sK2,sK3)
    | sK4 != k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))
    | sK3 != sK3
    | sK2 != k1_tsep_1(sK2,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_8548])).

cnf(c_12,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_26,plain,
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
    inference(cnf_transformation,[],[f79])).

cnf(c_63,negated_conjecture,
    ( r4_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_783,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X2)
    | sK5 != X0
    | sK6 != X3
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_63])).

cnf(c_784,plain,
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
    inference(unflattening,[status(thm)],[c_783])).

cnf(c_68,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_67,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_66,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_65,negated_conjecture,
    ( m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_788,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | sP1(sK5,sK2,X0,sK6,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_784,c_77,c_76,c_75,c_68,c_67,c_66,c_65])).

cnf(c_789,plain,
    ( sP1(sK5,sK2,X0,sK6,X1)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_788])).

cnf(c_1006,plain,
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
    inference(resolution_lifted,[status(thm)],[c_12,c_789])).

cnf(c_1007,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_1006])).

cnf(c_2499,plain,
    ( ~ sP0(X0_53,sK6,X0_54,sK2,sK5)
    | ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53))))
    | m1_subset_1(k2_tmap_1(sK2,X0_53,X0_54,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_53))))
    | v2_struct_0(X0_53)
    | ~ v2_pre_topc(X0_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_1007])).

cnf(c_3628,plain,
    ( sP0(X0_53,sK6,X0_54,sK2,sK5) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_53,X0_54,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_53)))) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2499])).

cnf(c_7537,plain,
    ( sP0(X0_53,sK6,X0_54,sK2,sK5) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_53,X0_54,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_2518,c_3628])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2549,plain,
    ( ~ r2_funct_2(X0_55,X1_55,X0_54,X1_54)
    | ~ v1_funct_2(X1_54,X0_55,X1_55)
    | ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X1_54)
    | ~ v1_funct_1(X0_54)
    | X0_54 = X1_54 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3579,plain,
    ( X0_54 = X1_54
    | r2_funct_2(X0_55,X1_55,X0_54,X1_54) != iProver_top
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | v1_funct_2(X1_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2549])).

cnf(c_4067,plain,
    ( sK4 = X0_54
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3614,c_3579])).

cnf(c_7527,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | sK4 = X0_54
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4067,c_84,c_85])).

cnf(c_7528,plain,
    ( sK4 = X0_54
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_7527])).

cnf(c_7667,plain,
    ( k2_tmap_1(sK2,sK3,X0_54,sK2) = sK4
    | sP0(sK3,sK6,X0_54,sK2,sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,X0_54,sK2)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,X0_54,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,X0_54,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7537,c_7528])).

cnf(c_7702,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4
    | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7667])).

cnf(c_4112,plain,
    ( X0_54 != X1_54
    | k2_tmap_1(sK2,X0_53,X2_54,k1_tsep_1(sK2,sK5,sK6)) != X1_54
    | k2_tmap_1(sK2,X0_53,X2_54,k1_tsep_1(sK2,sK5,sK6)) = X0_54 ),
    inference(instantiation,[status(thm)],[c_2558])).

cnf(c_7296,plain,
    ( X0_54 != k2_tmap_1(sK2,X0_53,X1_54,sK2)
    | k2_tmap_1(sK2,X1_53,X2_54,k1_tsep_1(sK2,sK5,sK6)) = X0_54
    | k2_tmap_1(sK2,X1_53,X2_54,k1_tsep_1(sK2,sK5,sK6)) != k2_tmap_1(sK2,X0_53,X1_54,sK2) ),
    inference(instantiation,[status(thm)],[c_4112])).

cnf(c_7297,plain,
    ( k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)) != k2_tmap_1(sK2,sK3,sK4,sK2)
    | k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)) = sK4
    | sK4 != k2_tmap_1(sK2,sK3,sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_7296])).

cnf(c_7168,plain,
    ( X0_54 != X1_54
    | X0_54 = k2_tmap_1(sK2,X0_53,X2_54,k1_tsep_1(sK2,sK5,sK6))
    | k2_tmap_1(sK2,X0_53,X2_54,k1_tsep_1(sK2,sK5,sK6)) != X1_54 ),
    inference(instantiation,[status(thm)],[c_2558])).

cnf(c_7169,plain,
    ( k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)) != sK4
    | sK4 = k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_7168])).

cnf(c_14,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_946,plain,
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
    inference(resolution_lifted,[status(thm)],[c_14,c_789])).

cnf(c_947,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_946])).

cnf(c_2501,plain,
    ( ~ sP0(X0_53,sK6,X0_54,sK2,sK5)
    | ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53))
    | v1_funct_2(k2_tmap_1(sK2,X0_53,X0_54,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53))))
    | v2_struct_0(X0_53)
    | ~ v2_pre_topc(X0_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_947])).

cnf(c_3626,plain,
    ( sP0(X0_53,sK6,X0_54,sK2,sK5) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_53,X0_54,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_53)) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2501])).

cnf(c_7023,plain,
    ( sP0(X0_53,sK6,X0_54,sK2,sK5) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_53,X0_54,sK2),u1_struct_0(sK2),u1_struct_0(X0_53)) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_2518,c_3626])).

cnf(c_7027,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7023])).

cnf(c_15,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_916,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_789])).

cnf(c_917,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X1)
    | v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(unflattening,[status(thm)],[c_916])).

cnf(c_2502,plain,
    ( ~ sP0(X0_53,sK6,X0_54,sK2,sK5)
    | ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53))))
    | v2_struct_0(X0_53)
    | ~ v2_pre_topc(X0_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k2_tmap_1(sK2,X0_53,X0_54,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(subtyping,[status(esa)],[c_917])).

cnf(c_3625,plain,
    ( sP0(X0_53,sK6,X0_54,sK2,sK5) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_53,X0_54,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2502])).

cnf(c_6780,plain,
    ( sP0(X0_53,sK6,X0_54,sK2,sK5) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_53,X0_54,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2518,c_3625])).

cnf(c_6783,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6780])).

cnf(c_2567,plain,
    ( X0_54 != X1_54
    | k2_tmap_1(X0_53,X1_53,X0_54,X2_53) = k2_tmap_1(X3_53,X4_53,X1_54,X5_53)
    | X0_53 != X3_53
    | X1_53 != X4_53
    | X2_53 != X5_53 ),
    theory(equality)).

cnf(c_4114,plain,
    ( X0_54 != X1_54
    | k2_tmap_1(sK2,X0_53,X0_54,k1_tsep_1(sK2,sK5,sK6)) = k2_tmap_1(X1_53,X2_53,X1_54,X3_53)
    | X0_53 != X2_53
    | k1_tsep_1(sK2,sK5,sK6) != X3_53
    | sK2 != X1_53 ),
    inference(instantiation,[status(thm)],[c_2567])).

cnf(c_4787,plain,
    ( X0_54 != X1_54
    | k2_tmap_1(sK2,X0_53,X0_54,k1_tsep_1(sK2,sK5,sK6)) = k2_tmap_1(sK2,X1_53,X1_54,X2_53)
    | X0_53 != X1_53
    | k1_tsep_1(sK2,sK5,sK6) != X2_53
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4114])).

cnf(c_6512,plain,
    ( X0_54 != X1_54
    | k2_tmap_1(sK2,X0_53,X0_54,k1_tsep_1(sK2,sK5,sK6)) = k2_tmap_1(sK2,X1_53,X1_54,sK2)
    | X0_53 != X1_53
    | k1_tsep_1(sK2,sK5,sK6) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4787])).

cnf(c_6513,plain,
    ( k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)) = k2_tmap_1(sK2,sK3,sK4,sK2)
    | sK4 != sK4
    | k1_tsep_1(sK2,sK5,sK6) != sK2
    | sK3 != sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_6512])).

cnf(c_2557,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_4986,plain,
    ( X0_53 != X1_53
    | X1_53 = X0_53 ),
    inference(resolution,[status(thm)],[c_2557,c_2552])).

cnf(c_5663,plain,
    ( sK2 = k1_tsep_1(sK2,sK5,sK6) ),
    inference(resolution,[status(thm)],[c_4986,c_2518])).

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
    inference(cnf_transformation,[],[f78])).

cnf(c_2538,plain,
    ( sP0(X0_53,X1_53,X0_54,X2_53,X3_53)
    | ~ v5_pre_topc(k2_tmap_1(X2_53,X0_53,X0_54,X1_53),X1_53,X0_53)
    | ~ v5_pre_topc(k2_tmap_1(X2_53,X0_53,X0_54,X3_53),X3_53,X0_53)
    | ~ v1_funct_2(k2_tmap_1(X2_53,X0_53,X0_54,X1_53),u1_struct_0(X1_53),u1_struct_0(X0_53))
    | ~ v1_funct_2(k2_tmap_1(X2_53,X0_53,X0_54,X3_53),u1_struct_0(X3_53),u1_struct_0(X0_53))
    | ~ m1_subset_1(k2_tmap_1(X2_53,X0_53,X0_54,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X0_53))))
    | ~ m1_subset_1(k2_tmap_1(X2_53,X0_53,X0_54,X3_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X0_53))))
    | ~ v1_funct_1(k2_tmap_1(X2_53,X0_53,X0_54,X1_53))
    | ~ v1_funct_1(k2_tmap_1(X2_53,X0_53,X0_54,X3_53)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_4223,plain,
    ( sP0(sK3,X0_53,sK4,sK2,sK5)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_53),X0_53,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_53),u1_struct_0(X0_53),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_53))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2538])).

cnf(c_5043,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_4223])).

cnf(c_5044,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5043])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2548,plain,
    ( ~ l1_pre_topc(X0_53)
    | l1_struct_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_4510,plain,
    ( ~ l1_pre_topc(sK5)
    | l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2548])).

cnf(c_4511,plain,
    ( l1_pre_topc(sK5) != iProver_top
    | l1_struct_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4510])).

cnf(c_4507,plain,
    ( ~ l1_pre_topc(sK6)
    | l1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2548])).

cnf(c_4508,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_struct_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4507])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2544,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | m1_subset_1(k2_tmap_1(X0_53,X1_53,X0_54,X2_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
    | ~ l1_struct_0(X2_53)
    | ~ l1_struct_0(X1_53)
    | ~ l1_struct_0(X0_53)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3866,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(X0_53)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2544])).

cnf(c_4492,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3866])).

cnf(c_4493,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4492])).

cnf(c_36,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_2525,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_3603,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2525])).

cnf(c_86,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_89,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66])).

cnf(c_90,plain,
    ( m1_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65])).

cnf(c_118,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_9,plain,
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
    inference(cnf_transformation,[],[f64])).

cnf(c_2541,plain,
    ( ~ v5_pre_topc(X0_54,X0_53,X1_53)
    | v5_pre_topc(k2_tmap_1(X0_53,X1_53,X0_54,X2_53),X2_53,X1_53)
    | ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X2_53,X0_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(X1_53)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_3911,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_53),X0_53,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_53,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2541])).

cnf(c_4029,plain,
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
    inference(instantiation,[status(thm)],[c_3911])).

cnf(c_4030,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4029])).

cnf(c_4443,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3603,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,c_89,c_90,c_118,c_4030])).

cnf(c_4445,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4443])).

cnf(c_2515,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(subtyping,[status(esa)],[c_67])).

cnf(c_3612,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2515])).

cnf(c_3581,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2547])).

cnf(c_4438,plain,
    ( l1_pre_topc(sK5) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3612,c_3581])).

cnf(c_4441,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4438])).

cnf(c_2517,negated_conjecture,
    ( m1_pre_topc(sK6,sK2) ),
    inference(subtyping,[status(esa)],[c_65])).

cnf(c_3610,plain,
    ( m1_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2517])).

cnf(c_4437,plain,
    ( l1_pre_topc(sK6) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3610,c_3581])).

cnf(c_4440,plain,
    ( l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4437])).

cnf(c_4408,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK6)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3866])).

cnf(c_4409,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4408])).

cnf(c_60,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2519,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_60])).

cnf(c_3609,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2519])).

cnf(c_87,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_68])).

cnf(c_88,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_67])).

cnf(c_94,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f62])).

cnf(c_2539,plain,
    ( ~ v5_pre_topc(X0_54,X0_53,X1_53)
    | ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X2_53,X0_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(X1_53)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k2_tmap_1(X0_53,X1_53,X0_54,X2_53)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_3871,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_53,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_53))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2539])).

cnf(c_3992,plain,
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
    inference(instantiation,[status(thm)],[c_3871])).

cnf(c_3993,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_3992])).

cnf(c_4247,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3609,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,c_87,c_88,c_94,c_3993])).

cnf(c_4249,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4247])).

cnf(c_44,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2523,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(subtyping,[status(esa)],[c_44])).

cnf(c_3605,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2523])).

cnf(c_110,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_3989,plain,
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
    inference(instantiation,[status(thm)],[c_3871])).

cnf(c_3990,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_3989])).

cnf(c_4242,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3605,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,c_89,c_90,c_110,c_3990])).

cnf(c_4244,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4242])).

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
    inference(cnf_transformation,[],[f130])).

cnf(c_500,plain,
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

cnf(c_501,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(renaming,[status(thm)],[c_500])).

cnf(c_2504,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(subtyping,[status(esa)],[c_501])).

cnf(c_10,plain,
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
    inference(cnf_transformation,[],[f63])).

cnf(c_2540,plain,
    ( ~ v5_pre_topc(X0_54,X0_53,X1_53)
    | ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | v1_funct_2(k2_tmap_1(X0_53,X1_53,X0_54,X2_53),u1_struct_0(X2_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X2_53,X0_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(X1_53)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3906,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_53),u1_struct_0(X0_53),u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_53,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2540])).

cnf(c_4019,plain,
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
    inference(instantiation,[status(thm)],[c_3906])).

cnf(c_4022,plain,
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
    inference(instantiation,[status(thm)],[c_3906])).

cnf(c_4032,plain,
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
    inference(instantiation,[status(thm)],[c_3911])).

cnf(c_4073,negated_conjecture,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2504,c_77,c_76,c_75,c_74,c_73,c_72,c_71,c_70,c_69,c_68,c_67,c_66,c_65,c_30,c_3989,c_3992,c_4019,c_4022,c_4029,c_4032])).

cnf(c_4075,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4073])).

cnf(c_4002,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3999])).

cnf(c_3972,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_2552])).

cnf(c_3938,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2548])).

cnf(c_3939,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3938])).

cnf(c_13,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_976,plain,
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
    inference(resolution_lifted,[status(thm)],[c_13,c_789])).

cnf(c_977,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_976])).

cnf(c_2500,plain,
    ( ~ sP0(X0_53,sK6,X0_54,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,X0_53,X0_54,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_53)
    | ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53))))
    | v2_struct_0(X0_53)
    | ~ v2_pre_topc(X0_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_977])).

cnf(c_2683,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2500])).

cnf(c_2553,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_2593,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2553])).

cnf(c_2592,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2552])).

cnf(c_194,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_196,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_194])).

cnf(c_195,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_40,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_114,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_52,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_102,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_56,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_98,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23907,c_8565,c_8550,c_7702,c_7297,c_7169,c_7027,c_6783,c_6513,c_5663,c_5044,c_5043,c_4511,c_4510,c_4508,c_4507,c_4493,c_4492,c_4445,c_4443,c_4441,c_4438,c_4440,c_4437,c_4409,c_4408,c_4249,c_4247,c_4244,c_4242,c_4075,c_4073,c_4002,c_3972,c_3939,c_3938,c_2683,c_2518,c_2593,c_2592,c_196,c_195,c_114,c_40,c_102,c_52,c_98,c_56,c_86,c_69,c_85,c_70,c_84,c_71,c_83,c_72,c_82,c_73,c_81,c_74,c_80,c_75,c_79,c_78])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.89/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.89/1.48  
% 7.89/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.89/1.48  
% 7.89/1.48  ------  iProver source info
% 7.89/1.48  
% 7.89/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.89/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.89/1.48  git: non_committed_changes: false
% 7.89/1.48  git: last_make_outside_of_git: false
% 7.89/1.48  
% 7.89/1.48  ------ 
% 7.89/1.48  ------ Parsing...
% 7.89/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.89/1.48  
% 7.89/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.89/1.48  
% 7.89/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.89/1.48  
% 7.89/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.89/1.48  ------ Proving...
% 7.89/1.48  ------ Problem Properties 
% 7.89/1.48  
% 7.89/1.48  
% 7.89/1.48  clauses                                 52
% 7.89/1.48  conjectures                             23
% 7.89/1.48  EPR                                     15
% 7.89/1.48  Horn                                    33
% 7.89/1.48  unary                                   14
% 7.89/1.48  binary                                  18
% 7.89/1.48  lits                                    227
% 7.89/1.48  lits eq                                 4
% 7.89/1.48  fd_pure                                 0
% 7.89/1.48  fd_pseudo                               0
% 7.89/1.48  fd_cond                                 0
% 7.89/1.48  fd_pseudo_cond                          1
% 7.89/1.48  AC symbols                              0
% 7.89/1.48  
% 7.89/1.48  ------ Input Options Time Limit: Unbounded
% 7.89/1.48  
% 7.89/1.48  
% 7.89/1.48  ------ 
% 7.89/1.48  Current options:
% 7.89/1.48  ------ 
% 7.89/1.48  
% 7.89/1.48  
% 7.89/1.48  
% 7.89/1.48  
% 7.89/1.48  ------ Proving...
% 7.89/1.48  
% 7.89/1.48  
% 7.89/1.48  % SZS status Theorem for theBenchmark.p
% 7.89/1.48  
% 7.89/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.89/1.48  
% 7.89/1.48  fof(f9,axiom,(
% 7.89/1.48    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.89/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f28,plain,(
% 7.89/1.48    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.89/1.48    inference(ennf_transformation,[],[f9])).
% 7.89/1.48  
% 7.89/1.48  fof(f80,plain,(
% 7.89/1.48    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f28])).
% 7.89/1.48  
% 7.89/1.48  fof(f12,conjecture,(
% 7.89/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 7.89/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f13,negated_conjecture,(
% 7.89/1.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 7.89/1.48    inference(negated_conjecture,[],[f12])).
% 7.89/1.48  
% 7.89/1.48  fof(f33,plain,(
% 7.89/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & (r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0)) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.89/1.48    inference(ennf_transformation,[],[f13])).
% 7.89/1.48  
% 7.89/1.48  fof(f34,plain,(
% 7.89/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.89/1.48    inference(flattening,[],[f33])).
% 7.89/1.48  
% 7.89/1.48  fof(f45,plain,(
% 7.89/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.89/1.48    inference(nnf_transformation,[],[f34])).
% 7.89/1.48  
% 7.89/1.48  fof(f46,plain,(
% 7.89/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.89/1.48    inference(flattening,[],[f45])).
% 7.89/1.48  
% 7.89/1.48  fof(f51,plain,(
% 7.89/1.48    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((~m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,sK6) & k1_tsep_1(X0,X3,sK6) = X0 & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 7.89/1.48    introduced(choice_axiom,[])).
% 7.89/1.48  
% 7.89/1.48  fof(f50,plain,(
% 7.89/1.48    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK5)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK5))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,sK5,X4) & k1_tsep_1(X0,sK5,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 7.89/1.48    introduced(choice_axiom,[])).
% 7.89/1.48  
% 7.89/1.48  fof(f49,plain,(
% 7.89/1.48    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(sK4,X0,X1) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) & m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X3))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK4,X0,X1) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 7.89/1.48    introduced(choice_axiom,[])).
% 7.89/1.48  
% 7.89/1.48  fof(f48,plain,(
% 7.89/1.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(X2,X0,sK3) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) & m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v5_pre_topc(X2,X0,sK3) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 7.89/1.48    introduced(choice_axiom,[])).
% 7.89/1.48  
% 7.89/1.48  fof(f47,plain,(
% 7.89/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(sK2,X3,X4) & k1_tsep_1(sK2,X3,X4) = sK2 & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 7.89/1.48    introduced(choice_axiom,[])).
% 7.89/1.48  
% 7.89/1.48  fof(f52,plain,(
% 7.89/1.48    (((((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,sK5,sK6) & k1_tsep_1(sK2,sK5,sK6) = sK2 & m1_pre_topc(sK6,sK2) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 7.89/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f46,f51,f50,f49,f48,f47])).
% 7.89/1.48  
% 7.89/1.48  fof(f91,plain,(
% 7.89/1.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f4,axiom,(
% 7.89/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 7.89/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f18,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.89/1.48    inference(ennf_transformation,[],[f4])).
% 7.89/1.48  
% 7.89/1.48  fof(f19,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(flattening,[],[f18])).
% 7.89/1.48  
% 7.89/1.48  fof(f57,plain,(
% 7.89/1.48    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f19])).
% 7.89/1.48  
% 7.89/1.48  fof(f83,plain,(
% 7.89/1.48    ~v2_struct_0(sK2)),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f84,plain,(
% 7.89/1.48    v2_pre_topc(sK2)),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f85,plain,(
% 7.89/1.48    l1_pre_topc(sK2)),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f86,plain,(
% 7.89/1.48    ~v2_struct_0(sK3)),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f87,plain,(
% 7.89/1.48    v2_pre_topc(sK3)),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f88,plain,(
% 7.89/1.48    l1_pre_topc(sK3)),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f89,plain,(
% 7.89/1.48    v1_funct_1(sK4)),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f90,plain,(
% 7.89/1.48    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f5,axiom,(
% 7.89/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 7.89/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f20,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.89/1.48    inference(ennf_transformation,[],[f5])).
% 7.89/1.48  
% 7.89/1.48  fof(f21,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(flattening,[],[f20])).
% 7.89/1.48  
% 7.89/1.48  fof(f58,plain,(
% 7.89/1.48    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f21])).
% 7.89/1.48  
% 7.89/1.48  fof(f96,plain,(
% 7.89/1.48    k1_tsep_1(sK2,sK5,sK6) = sK2),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f3,axiom,(
% 7.89/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.89/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f17,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.89/1.48    inference(ennf_transformation,[],[f3])).
% 7.89/1.48  
% 7.89/1.48  fof(f56,plain,(
% 7.89/1.48    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f17])).
% 7.89/1.48  
% 7.89/1.48  fof(f10,axiom,(
% 7.89/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 7.89/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f29,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.89/1.48    inference(ennf_transformation,[],[f10])).
% 7.89/1.48  
% 7.89/1.48  fof(f30,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(flattening,[],[f29])).
% 7.89/1.48  
% 7.89/1.48  fof(f81,plain,(
% 7.89/1.48    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f30])).
% 7.89/1.48  
% 7.89/1.48  fof(f36,plain,(
% 7.89/1.48    ! [X2,X0,X4,X3,X1] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> sP0(X1,X3,X4,X0,X2)) | ~sP1(X2,X0,X4,X3,X1))),
% 7.89/1.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 7.89/1.48  
% 7.89/1.48  fof(f39,plain,(
% 7.89/1.48    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))))) | ~sP1(X2,X0,X4,X3,X1))),
% 7.89/1.48    inference(nnf_transformation,[],[f36])).
% 7.89/1.48  
% 7.89/1.48  fof(f40,plain,(
% 7.89/1.48    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))))) | ~sP1(X2,X0,X4,X3,X1))),
% 7.89/1.48    inference(flattening,[],[f39])).
% 7.89/1.48  
% 7.89/1.48  fof(f41,plain,(
% 7.89/1.48    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) & v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) & v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) & v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))))) | ~sP1(X0,X1,X2,X3,X4))),
% 7.89/1.48    inference(rectify,[],[f40])).
% 7.89/1.48  
% 7.89/1.48  fof(f69,plain,(
% 7.89/1.48    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f41])).
% 7.89/1.48  
% 7.89/1.48  fof(f8,axiom,(
% 7.89/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))))))))),
% 7.89/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f26,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.89/1.48    inference(ennf_transformation,[],[f8])).
% 7.89/1.48  
% 7.89/1.48  fof(f27,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(flattening,[],[f26])).
% 7.89/1.48  
% 7.89/1.48  fof(f35,plain,(
% 7.89/1.48    ! [X1,X3,X4,X0,X2] : (sP0(X1,X3,X4,X0,X2) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))),
% 7.89/1.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.89/1.48  
% 7.89/1.48  fof(f37,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X2,X0,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(definition_folding,[],[f27,f36,f35])).
% 7.89/1.48  
% 7.89/1.48  fof(f79,plain,(
% 7.89/1.48    ( ! [X4,X2,X0,X3,X1] : (sP1(X2,X0,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f37])).
% 7.89/1.48  
% 7.89/1.48  fof(f97,plain,(
% 7.89/1.48    r4_tsep_1(sK2,sK5,sK6)),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f92,plain,(
% 7.89/1.48    ~v2_struct_0(sK5)),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f93,plain,(
% 7.89/1.48    m1_pre_topc(sK5,sK2)),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f94,plain,(
% 7.89/1.48    ~v2_struct_0(sK6)),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f95,plain,(
% 7.89/1.48    m1_pre_topc(sK6,sK2)),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f1,axiom,(
% 7.89/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 7.89/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f14,plain,(
% 7.89/1.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.89/1.48    inference(ennf_transformation,[],[f1])).
% 7.89/1.48  
% 7.89/1.48  fof(f15,plain,(
% 7.89/1.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.89/1.48    inference(flattening,[],[f14])).
% 7.89/1.48  
% 7.89/1.48  fof(f38,plain,(
% 7.89/1.48    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.89/1.48    inference(nnf_transformation,[],[f15])).
% 7.89/1.48  
% 7.89/1.48  fof(f53,plain,(
% 7.89/1.48    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f38])).
% 7.89/1.48  
% 7.89/1.48  fof(f67,plain,(
% 7.89/1.48    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f41])).
% 7.89/1.48  
% 7.89/1.48  fof(f66,plain,(
% 7.89/1.48    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f41])).
% 7.89/1.48  
% 7.89/1.48  fof(f42,plain,(
% 7.89/1.48    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 7.89/1.48    inference(nnf_transformation,[],[f35])).
% 7.89/1.48  
% 7.89/1.48  fof(f43,plain,(
% 7.89/1.48    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 7.89/1.48    inference(flattening,[],[f42])).
% 7.89/1.48  
% 7.89/1.48  fof(f44,plain,(
% 7.89/1.48    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) & ((m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 7.89/1.48    inference(rectify,[],[f43])).
% 7.89/1.48  
% 7.89/1.48  fof(f78,plain,(
% 7.89/1.48    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) )),
% 7.89/1.48    inference(cnf_transformation,[],[f44])).
% 7.89/1.48  
% 7.89/1.48  fof(f2,axiom,(
% 7.89/1.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.89/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f16,plain,(
% 7.89/1.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.89/1.48    inference(ennf_transformation,[],[f2])).
% 7.89/1.48  
% 7.89/1.48  fof(f55,plain,(
% 7.89/1.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f16])).
% 7.89/1.48  
% 7.89/1.48  fof(f6,axiom,(
% 7.89/1.48    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 7.89/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f22,plain,(
% 7.89/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 7.89/1.48    inference(ennf_transformation,[],[f6])).
% 7.89/1.48  
% 7.89/1.48  fof(f23,plain,(
% 7.89/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 7.89/1.48    inference(flattening,[],[f22])).
% 7.89/1.48  
% 7.89/1.48  fof(f61,plain,(
% 7.89/1.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f23])).
% 7.89/1.48  
% 7.89/1.48  fof(f124,plain,(
% 7.89/1.48    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f7,axiom,(
% 7.89/1.48    ! [X0,X1,X2,X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 7.89/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f24,plain,(
% 7.89/1.48    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.89/1.48    inference(ennf_transformation,[],[f7])).
% 7.89/1.48  
% 7.89/1.48  fof(f25,plain,(
% 7.89/1.48    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(flattening,[],[f24])).
% 7.89/1.48  
% 7.89/1.48  fof(f64,plain,(
% 7.89/1.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f25])).
% 7.89/1.48  
% 7.89/1.48  fof(f100,plain,(
% 7.89/1.48    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | v5_pre_topc(sK4,sK2,sK3)),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f62,plain,(
% 7.89/1.48    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f25])).
% 7.89/1.48  
% 7.89/1.48  fof(f116,plain,(
% 7.89/1.48    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | v5_pre_topc(sK4,sK2,sK3)),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f130,plain,(
% 7.89/1.48    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f63,plain,(
% 7.89/1.48    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f25])).
% 7.89/1.48  
% 7.89/1.48  fof(f68,plain,(
% 7.89/1.48    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f41])).
% 7.89/1.48  
% 7.89/1.48  fof(f120,plain,(
% 7.89/1.48    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f108,plain,(
% 7.89/1.48    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f104,plain,(
% 7.89/1.48    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 7.89/1.48    inference(cnf_transformation,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  cnf(c_27,plain,
% 7.89/1.48      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.89/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_2529,plain,
% 7.89/1.48      ( m1_pre_topc(X0_53,X0_53) | ~ l1_pre_topc(X0_53) ),
% 7.89/1.48      inference(subtyping,[status(esa)],[c_27]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_3599,plain,
% 7.89/1.48      ( m1_pre_topc(X0_53,X0_53) = iProver_top
% 7.89/1.48      | l1_pre_topc(X0_53) != iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_2529]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_69,negated_conjecture,
% 7.89/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 7.89/1.48      inference(cnf_transformation,[],[f91]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_2513,negated_conjecture,
% 7.89/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 7.89/1.48      inference(subtyping,[status(esa)],[c_69]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_3614,plain,
% 7.89/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_2513]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_4,plain,
% 7.89/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.89/1.48      | ~ m1_pre_topc(X3,X1)
% 7.89/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.89/1.48      | v2_struct_0(X1)
% 7.89/1.48      | v2_struct_0(X2)
% 7.89/1.48      | ~ v2_pre_topc(X2)
% 7.89/1.48      | ~ v2_pre_topc(X1)
% 7.89/1.48      | ~ l1_pre_topc(X1)
% 7.89/1.48      | ~ l1_pre_topc(X2)
% 7.89/1.48      | ~ v1_funct_1(X0)
% 7.89/1.48      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 7.89/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_2546,plain,
% 7.89/1.48      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 7.89/1.48      | ~ m1_pre_topc(X2_53,X0_53)
% 7.89/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 7.89/1.48      | v2_struct_0(X0_53)
% 7.89/1.48      | v2_struct_0(X1_53)
% 7.89/1.48      | ~ v2_pre_topc(X0_53)
% 7.89/1.48      | ~ v2_pre_topc(X1_53)
% 7.89/1.48      | ~ l1_pre_topc(X0_53)
% 7.89/1.48      | ~ l1_pre_topc(X1_53)
% 7.89/1.48      | ~ v1_funct_1(X0_54)
% 7.89/1.48      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,X0_54,X2_53) ),
% 7.89/1.48      inference(subtyping,[status(esa)],[c_4]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_3582,plain,
% 7.89/1.48      ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,X0_54,X2_53)
% 7.89/1.48      | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 7.89/1.48      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 7.89/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 7.89/1.48      | v2_struct_0(X1_53) = iProver_top
% 7.89/1.48      | v2_struct_0(X0_53) = iProver_top
% 7.89/1.48      | v2_pre_topc(X1_53) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_53) != iProver_top
% 7.89/1.48      | l1_pre_topc(X1_53) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_53) != iProver_top
% 7.89/1.48      | v1_funct_1(X0_54) != iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_2546]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_4579,plain,
% 7.89/1.48      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k2_tmap_1(sK2,sK3,sK4,X0_53)
% 7.89/1.48      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.89/1.48      | m1_pre_topc(X0_53,sK2) != iProver_top
% 7.89/1.48      | v2_struct_0(sK3) = iProver_top
% 7.89/1.48      | v2_struct_0(sK2) = iProver_top
% 7.89/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.89/1.48      | v2_pre_topc(sK2) != iProver_top
% 7.89/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.89/1.48      | l1_pre_topc(sK2) != iProver_top
% 7.89/1.48      | v1_funct_1(sK4) != iProver_top ),
% 7.89/1.48      inference(superposition,[status(thm)],[c_3614,c_3582]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_77,negated_conjecture,
% 7.89/1.48      ( ~ v2_struct_0(sK2) ),
% 7.89/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_78,plain,
% 7.89/1.48      ( v2_struct_0(sK2) != iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_77]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_76,negated_conjecture,
% 7.89/1.48      ( v2_pre_topc(sK2) ),
% 7.89/1.48      inference(cnf_transformation,[],[f84]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_79,plain,
% 7.89/1.48      ( v2_pre_topc(sK2) = iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_76]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_75,negated_conjecture,
% 7.89/1.48      ( l1_pre_topc(sK2) ),
% 7.89/1.48      inference(cnf_transformation,[],[f85]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_80,plain,
% 7.89/1.48      ( l1_pre_topc(sK2) = iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_75]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_74,negated_conjecture,
% 7.89/1.48      ( ~ v2_struct_0(sK3) ),
% 7.89/1.48      inference(cnf_transformation,[],[f86]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_81,plain,
% 7.89/1.48      ( v2_struct_0(sK3) != iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_74]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_73,negated_conjecture,
% 7.89/1.48      ( v2_pre_topc(sK3) ),
% 7.89/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_82,plain,
% 7.89/1.48      ( v2_pre_topc(sK3) = iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_73]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_72,negated_conjecture,
% 7.89/1.48      ( l1_pre_topc(sK3) ),
% 7.89/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_83,plain,
% 7.89/1.48      ( l1_pre_topc(sK3) = iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_72]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_71,negated_conjecture,
% 7.89/1.48      ( v1_funct_1(sK4) ),
% 7.89/1.48      inference(cnf_transformation,[],[f89]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_84,plain,
% 7.89/1.48      ( v1_funct_1(sK4) = iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_71]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_70,negated_conjecture,
% 7.89/1.48      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 7.89/1.48      inference(cnf_transformation,[],[f90]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_85,plain,
% 7.89/1.48      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_70]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_7896,plain,
% 7.89/1.48      ( m1_pre_topc(X0_53,sK2) != iProver_top
% 7.89/1.48      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k2_tmap_1(sK2,sK3,sK4,X0_53) ),
% 7.89/1.48      inference(global_propositional_subsumption,
% 7.89/1.48                [status(thm)],
% 7.89/1.48                [c_4579,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_7897,plain,
% 7.89/1.48      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k2_tmap_1(sK2,sK3,sK4,X0_53)
% 7.89/1.48      | m1_pre_topc(X0_53,sK2) != iProver_top ),
% 7.89/1.48      inference(renaming,[status(thm)],[c_7896]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_7904,plain,
% 7.89/1.48      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK3,sK4,sK2)
% 7.89/1.48      | l1_pre_topc(sK2) != iProver_top ),
% 7.89/1.48      inference(superposition,[status(thm)],[c_3599,c_7897]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_3999,plain,
% 7.89/1.48      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 7.89/1.48      inference(instantiation,[status(thm)],[c_2529]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_3876,plain,
% 7.89/1.48      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.89/1.48      | ~ m1_pre_topc(X0_53,sK2)
% 7.89/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.89/1.48      | v2_struct_0(sK3)
% 7.89/1.48      | v2_struct_0(sK2)
% 7.89/1.48      | ~ v2_pre_topc(sK3)
% 7.89/1.48      | ~ v2_pre_topc(sK2)
% 7.89/1.48      | ~ l1_pre_topc(sK3)
% 7.89/1.48      | ~ l1_pre_topc(sK2)
% 7.89/1.48      | ~ v1_funct_1(sK4)
% 7.89/1.48      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k2_tmap_1(sK2,sK3,sK4,X0_53) ),
% 7.89/1.48      inference(instantiation,[status(thm)],[c_2546]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_4419,plain,
% 7.89/1.48      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.89/1.48      | ~ m1_pre_topc(sK2,sK2)
% 7.89/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.89/1.48      | v2_struct_0(sK3)
% 7.89/1.48      | v2_struct_0(sK2)
% 7.89/1.48      | ~ v2_pre_topc(sK3)
% 7.89/1.48      | ~ v2_pre_topc(sK2)
% 7.89/1.48      | ~ l1_pre_topc(sK3)
% 7.89/1.48      | ~ l1_pre_topc(sK2)
% 7.89/1.48      | ~ v1_funct_1(sK4)
% 7.89/1.48      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK3,sK4,sK2) ),
% 7.89/1.48      inference(instantiation,[status(thm)],[c_3876]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_8150,plain,
% 7.89/1.48      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK3,sK4,sK2) ),
% 7.89/1.48      inference(global_propositional_subsumption,
% 7.89/1.48                [status(thm)],
% 7.89/1.48                [c_7904,c_77,c_76,c_75,c_74,c_73,c_72,c_71,c_70,c_69,
% 7.89/1.48                 c_3999,c_4419]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_5,plain,
% 7.89/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.89/1.48      | ~ m1_pre_topc(X3,X4)
% 7.89/1.48      | ~ m1_pre_topc(X3,X1)
% 7.89/1.48      | ~ m1_pre_topc(X1,X4)
% 7.89/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.89/1.48      | v2_struct_0(X4)
% 7.89/1.48      | v2_struct_0(X2)
% 7.89/1.48      | ~ v2_pre_topc(X2)
% 7.89/1.48      | ~ v2_pre_topc(X4)
% 7.89/1.48      | ~ l1_pre_topc(X4)
% 7.89/1.48      | ~ l1_pre_topc(X2)
% 7.89/1.48      | ~ v1_funct_1(X0)
% 7.89/1.48      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 7.89/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2545,plain,
% 7.89/1.49      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 7.89/1.49      | ~ m1_pre_topc(X2_53,X0_53)
% 7.89/1.49      | ~ m1_pre_topc(X0_53,X3_53)
% 7.89/1.49      | ~ m1_pre_topc(X2_53,X3_53)
% 7.89/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 7.89/1.49      | v2_struct_0(X3_53)
% 7.89/1.49      | v2_struct_0(X1_53)
% 7.89/1.49      | ~ v2_pre_topc(X1_53)
% 7.89/1.49      | ~ v2_pre_topc(X3_53)
% 7.89/1.49      | ~ l1_pre_topc(X1_53)
% 7.89/1.49      | ~ l1_pre_topc(X3_53)
% 7.89/1.49      | ~ v1_funct_1(X0_54)
% 7.89/1.49      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_54) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3583,plain,
% 7.89/1.49      ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_54)
% 7.89/1.49      | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 7.89/1.49      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 7.89/1.49      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 7.89/1.49      | m1_pre_topc(X2_53,X3_53) != iProver_top
% 7.89/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 7.89/1.49      | v2_struct_0(X3_53) = iProver_top
% 7.89/1.49      | v2_struct_0(X1_53) = iProver_top
% 7.89/1.49      | v2_pre_topc(X1_53) != iProver_top
% 7.89/1.49      | v2_pre_topc(X3_53) != iProver_top
% 7.89/1.49      | l1_pre_topc(X1_53) != iProver_top
% 7.89/1.49      | l1_pre_topc(X3_53) != iProver_top
% 7.89/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_2545]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4791,plain,
% 7.89/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK3,sK2,X0_53,sK4)
% 7.89/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.89/1.49      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 7.89/1.49      | m1_pre_topc(X0_53,sK2) != iProver_top
% 7.89/1.49      | m1_pre_topc(sK2,X1_53) != iProver_top
% 7.89/1.49      | v2_struct_0(X1_53) = iProver_top
% 7.89/1.49      | v2_struct_0(sK3) = iProver_top
% 7.89/1.49      | v2_pre_topc(X1_53) != iProver_top
% 7.89/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.89/1.49      | l1_pre_topc(X1_53) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.89/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_3614,c_3583]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_8054,plain,
% 7.89/1.49      ( v2_pre_topc(X1_53) != iProver_top
% 7.89/1.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK3,sK2,X0_53,sK4)
% 7.89/1.49      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 7.89/1.49      | m1_pre_topc(X0_53,sK2) != iProver_top
% 7.89/1.49      | m1_pre_topc(sK2,X1_53) != iProver_top
% 7.89/1.49      | v2_struct_0(X1_53) = iProver_top
% 7.89/1.49      | l1_pre_topc(X1_53) != iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_4791,c_81,c_82,c_83,c_84,c_85]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_8055,plain,
% 7.89/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK3,sK2,X0_53,sK4)
% 7.89/1.49      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 7.89/1.49      | m1_pre_topc(X0_53,sK2) != iProver_top
% 7.89/1.49      | m1_pre_topc(sK2,X1_53) != iProver_top
% 7.89/1.49      | v2_struct_0(X1_53) = iProver_top
% 7.89/1.49      | v2_pre_topc(X1_53) != iProver_top
% 7.89/1.49      | l1_pre_topc(X1_53) != iProver_top ),
% 7.89/1.49      inference(renaming,[status(thm)],[c_8054]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_8062,plain,
% 7.89/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X0_53,sK3,sK2,X0_53,sK4)
% 7.89/1.49      | m1_pre_topc(X0_53,sK2) != iProver_top
% 7.89/1.49      | m1_pre_topc(sK2,X0_53) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_53) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_53) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_53) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_3599,c_8055]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2565,plain,
% 7.89/1.49      ( ~ l1_pre_topc(X0_53) | l1_pre_topc(X1_53) | X1_53 != X0_53 ),
% 7.89/1.49      theory(equality) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_64,negated_conjecture,
% 7.89/1.49      ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
% 7.89/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2518,negated_conjecture,
% 7.89/1.49      ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_64]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4532,plain,
% 7.89/1.49      ( l1_pre_topc(k1_tsep_1(sK2,sK5,sK6)) | ~ l1_pre_topc(sK2) ),
% 7.89/1.49      inference(resolution,[status(thm)],[c_2565,c_2518]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4533,plain,
% 7.89/1.49      ( l1_pre_topc(k1_tsep_1(sK2,sK5,sK6)) = iProver_top
% 7.89/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_4532]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2566,plain,
% 7.89/1.49      ( ~ m1_pre_topc(X0_53,X1_53)
% 7.89/1.49      | m1_pre_topc(X2_53,X3_53)
% 7.89/1.49      | X2_53 != X0_53
% 7.89/1.49      | X3_53 != X1_53 ),
% 7.89/1.49      theory(equality) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_5092,plain,
% 7.89/1.49      ( m1_pre_topc(X0_53,k1_tsep_1(sK2,sK5,sK6))
% 7.89/1.49      | ~ m1_pre_topc(X1_53,sK2)
% 7.89/1.49      | X0_53 != X1_53 ),
% 7.89/1.49      inference(resolution,[status(thm)],[c_2566,c_2518]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2552,plain,( X0_53 = X0_53 ),theory(equality) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_5236,plain,
% 7.89/1.49      ( m1_pre_topc(X0_53,k1_tsep_1(sK2,sK5,sK6))
% 7.89/1.49      | ~ m1_pre_topc(X0_53,sK2) ),
% 7.89/1.49      inference(resolution,[status(thm)],[c_5092,c_2552]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3,plain,
% 7.89/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.89/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2547,plain,
% 7.89/1.49      ( ~ m1_pre_topc(X0_53,X1_53)
% 7.89/1.49      | ~ l1_pre_topc(X1_53)
% 7.89/1.49      | l1_pre_topc(X0_53) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_5293,plain,
% 7.89/1.49      ( ~ m1_pre_topc(X0_53,sK2)
% 7.89/1.49      | l1_pre_topc(X0_53)
% 7.89/1.49      | ~ l1_pre_topc(k1_tsep_1(sK2,sK5,sK6)) ),
% 7.89/1.49      inference(resolution,[status(thm)],[c_5236,c_2547]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_5294,plain,
% 7.89/1.49      ( m1_pre_topc(X0_53,sK2) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_53) = iProver_top
% 7.89/1.49      | l1_pre_topc(k1_tsep_1(sK2,sK5,sK6)) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_5293]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_8455,plain,
% 7.89/1.49      ( v2_pre_topc(X0_53) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_53) = iProver_top
% 7.89/1.49      | m1_pre_topc(sK2,X0_53) != iProver_top
% 7.89/1.49      | m1_pre_topc(X0_53,sK2) != iProver_top
% 7.89/1.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X0_53,sK3,sK2,X0_53,sK4) ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_8062,c_80,c_4533,c_5294]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_8456,plain,
% 7.89/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X0_53,sK3,sK2,X0_53,sK4)
% 7.89/1.49      | m1_pre_topc(X0_53,sK2) != iProver_top
% 7.89/1.49      | m1_pre_topc(sK2,X0_53) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_53) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_53) != iProver_top ),
% 7.89/1.49      inference(renaming,[status(thm)],[c_8455]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_8463,plain,
% 7.89/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK2,sK3,sK2,sK2,sK4)
% 7.89/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.89/1.49      | v2_struct_0(sK2) = iProver_top
% 7.89/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_3599,c_8456]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3916,plain,
% 7.89/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.89/1.49      | ~ m1_pre_topc(X0_53,X1_53)
% 7.89/1.49      | ~ m1_pre_topc(X0_53,sK2)
% 7.89/1.49      | ~ m1_pre_topc(sK2,X1_53)
% 7.89/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.89/1.49      | v2_struct_0(X1_53)
% 7.89/1.49      | v2_struct_0(sK3)
% 7.89/1.49      | ~ v2_pre_topc(X1_53)
% 7.89/1.49      | ~ v2_pre_topc(sK3)
% 7.89/1.49      | ~ l1_pre_topc(X1_53)
% 7.89/1.49      | ~ l1_pre_topc(sK3)
% 7.89/1.49      | ~ v1_funct_1(sK4)
% 7.89/1.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK3,sK2,X0_53,sK4) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2545]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4430,plain,
% 7.89/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.89/1.49      | ~ m1_pre_topc(X0_53,sK2)
% 7.89/1.49      | ~ m1_pre_topc(sK2,sK2)
% 7.89/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.89/1.49      | v2_struct_0(sK3)
% 7.89/1.49      | v2_struct_0(sK2)
% 7.89/1.49      | ~ v2_pre_topc(sK3)
% 7.89/1.49      | ~ v2_pre_topc(sK2)
% 7.89/1.49      | ~ l1_pre_topc(sK3)
% 7.89/1.49      | ~ l1_pre_topc(sK2)
% 7.89/1.49      | ~ v1_funct_1(sK4)
% 7.89/1.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_53)) = k3_tmap_1(sK2,sK3,sK2,X0_53,sK4) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_3916]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_5006,plain,
% 7.89/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.89/1.49      | ~ m1_pre_topc(sK2,sK2)
% 7.89/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.89/1.49      | v2_struct_0(sK3)
% 7.89/1.49      | v2_struct_0(sK2)
% 7.89/1.49      | ~ v2_pre_topc(sK3)
% 7.89/1.49      | ~ v2_pre_topc(sK2)
% 7.89/1.49      | ~ l1_pre_topc(sK3)
% 7.89/1.49      | ~ l1_pre_topc(sK2)
% 7.89/1.49      | ~ v1_funct_1(sK4)
% 7.89/1.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK2,sK3,sK2,sK2,sK4) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_4430]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_8639,plain,
% 7.89/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK2,sK3,sK2,sK2,sK4) ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_8463,c_77,c_76,c_75,c_74,c_73,c_72,c_71,c_70,c_69,
% 7.89/1.49                 c_3999,c_5006]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_8641,plain,
% 7.89/1.49      ( k3_tmap_1(sK2,sK3,sK2,sK2,sK4) = k2_tmap_1(sK2,sK3,sK4,sK2) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_8150,c_8639]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_28,plain,
% 7.89/1.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
% 7.89/1.49      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 7.89/1.49      | ~ m1_pre_topc(X0,X3)
% 7.89/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.89/1.49      | v2_struct_0(X3)
% 7.89/1.49      | v2_struct_0(X1)
% 7.89/1.49      | v2_struct_0(X0)
% 7.89/1.49      | ~ v2_pre_topc(X1)
% 7.89/1.49      | ~ v2_pre_topc(X3)
% 7.89/1.49      | ~ l1_pre_topc(X3)
% 7.89/1.49      | ~ l1_pre_topc(X1)
% 7.89/1.49      | ~ v1_funct_1(X2) ),
% 7.89/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2528,plain,
% 7.89/1.49      ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,k3_tmap_1(X2_53,X1_53,X0_53,X0_53,X0_54))
% 7.89/1.49      | ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 7.89/1.49      | ~ m1_pre_topc(X0_53,X2_53)
% 7.89/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 7.89/1.49      | v2_struct_0(X0_53)
% 7.89/1.49      | v2_struct_0(X1_53)
% 7.89/1.49      | v2_struct_0(X2_53)
% 7.89/1.49      | ~ v2_pre_topc(X1_53)
% 7.89/1.49      | ~ v2_pre_topc(X2_53)
% 7.89/1.49      | ~ l1_pre_topc(X1_53)
% 7.89/1.49      | ~ l1_pre_topc(X2_53)
% 7.89/1.49      | ~ v1_funct_1(X0_54) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_28]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3600,plain,
% 7.89/1.49      ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,k3_tmap_1(X2_53,X1_53,X0_53,X0_53,X0_54)) = iProver_top
% 7.89/1.49      | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 7.89/1.49      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 7.89/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 7.89/1.49      | v2_struct_0(X1_53) = iProver_top
% 7.89/1.49      | v2_struct_0(X0_53) = iProver_top
% 7.89/1.49      | v2_struct_0(X2_53) = iProver_top
% 7.89/1.49      | v2_pre_topc(X1_53) != iProver_top
% 7.89/1.49      | v2_pre_topc(X2_53) != iProver_top
% 7.89/1.49      | l1_pre_topc(X1_53) != iProver_top
% 7.89/1.49      | l1_pre_topc(X2_53) != iProver_top
% 7.89/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_2528]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_23907,plain,
% 7.89/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top
% 7.89/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.89/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.89/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.89/1.49      | v2_struct_0(sK3) = iProver_top
% 7.89/1.49      | v2_struct_0(sK2) = iProver_top
% 7.89/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.89/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.89/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_8641,c_3600]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2558,plain,
% 7.89/1.49      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 7.89/1.49      theory(equality) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_8564,plain,
% 7.89/1.49      ( X0_54 != X1_54
% 7.89/1.49      | X0_54 = k2_tmap_1(sK2,X0_53,X2_54,sK2)
% 7.89/1.49      | k2_tmap_1(sK2,X0_53,X2_54,sK2) != X1_54 ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2558]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_8565,plain,
% 7.89/1.49      ( k2_tmap_1(sK2,sK3,sK4,sK2) != sK4
% 7.89/1.49      | sK4 = k2_tmap_1(sK2,sK3,sK4,sK2)
% 7.89/1.49      | sK4 != sK4 ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_8564]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2572,plain,
% 7.89/1.49      ( ~ v5_pre_topc(X0_54,X0_53,X1_53)
% 7.89/1.49      | v5_pre_topc(X1_54,X2_53,X3_53)
% 7.89/1.49      | X1_54 != X0_54
% 7.89/1.49      | X2_53 != X0_53
% 7.89/1.49      | X3_53 != X1_53 ),
% 7.89/1.49      theory(equality) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4310,plain,
% 7.89/1.49      ( v5_pre_topc(X0_54,X0_53,X1_53)
% 7.89/1.49      | ~ v5_pre_topc(X1_54,k1_tsep_1(sK2,sK5,sK6),X2_53)
% 7.89/1.49      | X0_54 != X1_54
% 7.89/1.49      | X1_53 != X2_53
% 7.89/1.49      | X0_53 != k1_tsep_1(sK2,sK5,sK6) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2572]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_7202,plain,
% 7.89/1.49      ( ~ v5_pre_topc(X0_54,k1_tsep_1(sK2,sK5,sK6),X0_53)
% 7.89/1.49      | v5_pre_topc(X1_54,sK2,X1_53)
% 7.89/1.49      | X1_54 != X0_54
% 7.89/1.49      | X1_53 != X0_53
% 7.89/1.49      | sK2 != k1_tsep_1(sK2,sK5,sK6) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_4310]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_8548,plain,
% 7.89/1.49      ( v5_pre_topc(X0_54,sK2,X0_53)
% 7.89/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,X1_53,X1_54,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X1_53)
% 7.89/1.49      | X0_54 != k2_tmap_1(sK2,X1_53,X1_54,k1_tsep_1(sK2,sK5,sK6))
% 7.89/1.49      | X0_53 != X1_53
% 7.89/1.49      | sK2 != k1_tsep_1(sK2,sK5,sK6) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_7202]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_8550,plain,
% 7.89/1.49      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
% 7.89/1.49      | v5_pre_topc(sK4,sK2,sK3)
% 7.89/1.49      | sK4 != k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))
% 7.89/1.49      | sK3 != sK3
% 7.89/1.49      | sK2 != k1_tsep_1(sK2,sK5,sK6) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_8548]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_12,plain,
% 7.89/1.49      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.89/1.49      | ~ sP0(X4,X3,X2,X1,X0)
% 7.89/1.49      | m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) ),
% 7.89/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_26,plain,
% 7.89/1.49      ( sP1(X0,X1,X2,X3,X4)
% 7.89/1.49      | ~ r4_tsep_1(X1,X0,X3)
% 7.89/1.49      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
% 7.89/1.49      | ~ m1_pre_topc(X3,X1)
% 7.89/1.49      | ~ m1_pre_topc(X0,X1)
% 7.89/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 7.89/1.49      | v2_struct_0(X1)
% 7.89/1.49      | v2_struct_0(X4)
% 7.89/1.49      | v2_struct_0(X3)
% 7.89/1.49      | v2_struct_0(X0)
% 7.89/1.49      | ~ v2_pre_topc(X4)
% 7.89/1.49      | ~ v2_pre_topc(X1)
% 7.89/1.49      | ~ l1_pre_topc(X1)
% 7.89/1.49      | ~ l1_pre_topc(X4)
% 7.89/1.49      | ~ v1_funct_1(X2) ),
% 7.89/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_63,negated_conjecture,
% 7.89/1.49      ( r4_tsep_1(sK2,sK5,sK6) ),
% 7.89/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_783,plain,
% 7.89/1.49      ( sP1(X0,X1,X2,X3,X4)
% 7.89/1.49      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
% 7.89/1.49      | ~ m1_pre_topc(X0,X1)
% 7.89/1.49      | ~ m1_pre_topc(X3,X1)
% 7.89/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 7.89/1.49      | v2_struct_0(X0)
% 7.89/1.49      | v2_struct_0(X1)
% 7.89/1.49      | v2_struct_0(X4)
% 7.89/1.49      | v2_struct_0(X3)
% 7.89/1.49      | ~ v2_pre_topc(X1)
% 7.89/1.49      | ~ v2_pre_topc(X4)
% 7.89/1.49      | ~ l1_pre_topc(X1)
% 7.89/1.49      | ~ l1_pre_topc(X4)
% 7.89/1.49      | ~ v1_funct_1(X2)
% 7.89/1.49      | sK5 != X0
% 7.89/1.49      | sK6 != X3
% 7.89/1.49      | sK2 != X1 ),
% 7.89/1.49      inference(resolution_lifted,[status(thm)],[c_26,c_63]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_784,plain,
% 7.89/1.49      ( sP1(sK5,sK2,X0,sK6,X1)
% 7.89/1.49      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 7.89/1.49      | ~ m1_pre_topc(sK5,sK2)
% 7.89/1.49      | ~ m1_pre_topc(sK6,sK2)
% 7.89/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 7.89/1.49      | v2_struct_0(X1)
% 7.89/1.49      | v2_struct_0(sK5)
% 7.89/1.49      | v2_struct_0(sK6)
% 7.89/1.49      | v2_struct_0(sK2)
% 7.89/1.49      | ~ v2_pre_topc(X1)
% 7.89/1.49      | ~ v2_pre_topc(sK2)
% 7.89/1.49      | ~ l1_pre_topc(X1)
% 7.89/1.49      | ~ l1_pre_topc(sK2)
% 7.89/1.49      | ~ v1_funct_1(X0) ),
% 7.89/1.49      inference(unflattening,[status(thm)],[c_783]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_68,negated_conjecture,
% 7.89/1.49      ( ~ v2_struct_0(sK5) ),
% 7.89/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_67,negated_conjecture,
% 7.89/1.49      ( m1_pre_topc(sK5,sK2) ),
% 7.89/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_66,negated_conjecture,
% 7.89/1.49      ( ~ v2_struct_0(sK6) ),
% 7.89/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_65,negated_conjecture,
% 7.89/1.49      ( m1_pre_topc(sK6,sK2) ),
% 7.89/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_788,plain,
% 7.89/1.49      ( ~ l1_pre_topc(X1)
% 7.89/1.49      | v2_struct_0(X1)
% 7.89/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 7.89/1.49      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 7.89/1.49      | sP1(sK5,sK2,X0,sK6,X1)
% 7.89/1.49      | ~ v2_pre_topc(X1)
% 7.89/1.49      | ~ v1_funct_1(X0) ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_784,c_77,c_76,c_75,c_68,c_67,c_66,c_65]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_789,plain,
% 7.89/1.49      ( sP1(sK5,sK2,X0,sK6,X1)
% 7.89/1.49      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 7.89/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 7.89/1.49      | v2_struct_0(X1)
% 7.89/1.49      | ~ v2_pre_topc(X1)
% 7.89/1.49      | ~ l1_pre_topc(X1)
% 7.89/1.49      | ~ v1_funct_1(X0) ),
% 7.89/1.49      inference(renaming,[status(thm)],[c_788]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1006,plain,
% 7.89/1.49      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.89/1.49      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 7.89/1.49      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 7.89/1.49      | m1_subset_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))))
% 7.89/1.49      | v2_struct_0(X6)
% 7.89/1.49      | ~ v2_pre_topc(X6)
% 7.89/1.49      | ~ l1_pre_topc(X6)
% 7.89/1.49      | ~ v1_funct_1(X5)
% 7.89/1.49      | X5 != X2
% 7.89/1.49      | X6 != X0
% 7.89/1.49      | sK5 != X4
% 7.89/1.49      | sK6 != X1
% 7.89/1.49      | sK2 != X3 ),
% 7.89/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_789]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1007,plain,
% 7.89/1.49      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 7.89/1.49      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 7.89/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 7.89/1.49      | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
% 7.89/1.49      | v2_struct_0(X0)
% 7.89/1.49      | ~ v2_pre_topc(X0)
% 7.89/1.49      | ~ l1_pre_topc(X0)
% 7.89/1.49      | ~ v1_funct_1(X1) ),
% 7.89/1.49      inference(unflattening,[status(thm)],[c_1006]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2499,plain,
% 7.89/1.49      ( ~ sP0(X0_53,sK6,X0_54,sK2,sK5)
% 7.89/1.49      | ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53))
% 7.89/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53))))
% 7.89/1.49      | m1_subset_1(k2_tmap_1(sK2,X0_53,X0_54,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_53))))
% 7.89/1.49      | v2_struct_0(X0_53)
% 7.89/1.49      | ~ v2_pre_topc(X0_53)
% 7.89/1.49      | ~ l1_pre_topc(X0_53)
% 7.89/1.49      | ~ v1_funct_1(X0_54) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_1007]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3628,plain,
% 7.89/1.49      ( sP0(X0_53,sK6,X0_54,sK2,sK5) != iProver_top
% 7.89/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
% 7.89/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
% 7.89/1.49      | m1_subset_1(k2_tmap_1(sK2,X0_53,X0_54,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_53)))) = iProver_top
% 7.89/1.49      | v2_struct_0(X0_53) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_53) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_53) != iProver_top
% 7.89/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_2499]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_7537,plain,
% 7.89/1.49      ( sP0(X0_53,sK6,X0_54,sK2,sK5) != iProver_top
% 7.89/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
% 7.89/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
% 7.89/1.49      | m1_subset_1(k2_tmap_1(sK2,X0_53,X0_54,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) = iProver_top
% 7.89/1.49      | v2_struct_0(X0_53) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_53) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_53) != iProver_top
% 7.89/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_2518,c_3628]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1,plain,
% 7.89/1.49      ( ~ r2_funct_2(X0,X1,X2,X3)
% 7.89/1.49      | ~ v1_funct_2(X3,X0,X1)
% 7.89/1.49      | ~ v1_funct_2(X2,X0,X1)
% 7.89/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.89/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.89/1.49      | ~ v1_funct_1(X3)
% 7.89/1.49      | ~ v1_funct_1(X2)
% 7.89/1.49      | X2 = X3 ),
% 7.89/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2549,plain,
% 7.89/1.49      ( ~ r2_funct_2(X0_55,X1_55,X0_54,X1_54)
% 7.89/1.49      | ~ v1_funct_2(X1_54,X0_55,X1_55)
% 7.89/1.49      | ~ v1_funct_2(X0_54,X0_55,X1_55)
% 7.89/1.49      | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 7.89/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 7.89/1.49      | ~ v1_funct_1(X1_54)
% 7.89/1.49      | ~ v1_funct_1(X0_54)
% 7.89/1.49      | X0_54 = X1_54 ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3579,plain,
% 7.89/1.49      ( X0_54 = X1_54
% 7.89/1.49      | r2_funct_2(X0_55,X1_55,X0_54,X1_54) != iProver_top
% 7.89/1.49      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 7.89/1.49      | v1_funct_2(X1_54,X0_55,X1_55) != iProver_top
% 7.89/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 7.89/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 7.89/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.89/1.49      | v1_funct_1(X1_54) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_2549]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4067,plain,
% 7.89/1.49      ( sK4 = X0_54
% 7.89/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_54) != iProver_top
% 7.89/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.89/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.89/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.89/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.89/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_3614,c_3579]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_7527,plain,
% 7.89/1.49      ( v1_funct_1(X0_54) != iProver_top
% 7.89/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.89/1.49      | sK4 = X0_54
% 7.89/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_54) != iProver_top
% 7.89/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_4067,c_84,c_85]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_7528,plain,
% 7.89/1.49      ( sK4 = X0_54
% 7.89/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_54) != iProver_top
% 7.89/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.89/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.89/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.89/1.49      inference(renaming,[status(thm)],[c_7527]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_7667,plain,
% 7.89/1.49      ( k2_tmap_1(sK2,sK3,X0_54,sK2) = sK4
% 7.89/1.49      | sP0(sK3,sK6,X0_54,sK2,sK5) != iProver_top
% 7.89/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,X0_54,sK2)) != iProver_top
% 7.89/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.89/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,X0_54,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.89/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.89/1.49      | v2_struct_0(sK3) = iProver_top
% 7.89/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.89/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,X0_54,sK2)) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_7537,c_7528]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_7702,plain,
% 7.89/1.49      ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4
% 7.89/1.49      | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.89/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
% 7.89/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.89/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.89/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.89/1.49      | v2_struct_0(sK3) = iProver_top
% 7.89/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
% 7.89/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_7667]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4112,plain,
% 7.89/1.49      ( X0_54 != X1_54
% 7.89/1.49      | k2_tmap_1(sK2,X0_53,X2_54,k1_tsep_1(sK2,sK5,sK6)) != X1_54
% 7.89/1.49      | k2_tmap_1(sK2,X0_53,X2_54,k1_tsep_1(sK2,sK5,sK6)) = X0_54 ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2558]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_7296,plain,
% 7.89/1.49      ( X0_54 != k2_tmap_1(sK2,X0_53,X1_54,sK2)
% 7.89/1.49      | k2_tmap_1(sK2,X1_53,X2_54,k1_tsep_1(sK2,sK5,sK6)) = X0_54
% 7.89/1.49      | k2_tmap_1(sK2,X1_53,X2_54,k1_tsep_1(sK2,sK5,sK6)) != k2_tmap_1(sK2,X0_53,X1_54,sK2) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_4112]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_7297,plain,
% 7.89/1.49      ( k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)) != k2_tmap_1(sK2,sK3,sK4,sK2)
% 7.89/1.49      | k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)) = sK4
% 7.89/1.49      | sK4 != k2_tmap_1(sK2,sK3,sK4,sK2) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_7296]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_7168,plain,
% 7.89/1.49      ( X0_54 != X1_54
% 7.89/1.49      | X0_54 = k2_tmap_1(sK2,X0_53,X2_54,k1_tsep_1(sK2,sK5,sK6))
% 7.89/1.49      | k2_tmap_1(sK2,X0_53,X2_54,k1_tsep_1(sK2,sK5,sK6)) != X1_54 ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2558]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_7169,plain,
% 7.89/1.49      ( k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)) != sK4
% 7.89/1.49      | sK4 = k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))
% 7.89/1.49      | sK4 != sK4 ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_7168]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_14,plain,
% 7.89/1.49      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.89/1.49      | ~ sP0(X4,X3,X2,X1,X0)
% 7.89/1.49      | v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) ),
% 7.89/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_946,plain,
% 7.89/1.49      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.89/1.49      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 7.89/1.49      | v1_funct_2(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))
% 7.89/1.49      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 7.89/1.49      | v2_struct_0(X6)
% 7.89/1.49      | ~ v2_pre_topc(X6)
% 7.89/1.49      | ~ l1_pre_topc(X6)
% 7.89/1.49      | ~ v1_funct_1(X5)
% 7.89/1.49      | X5 != X2
% 7.89/1.49      | X6 != X0
% 7.89/1.49      | sK5 != X4
% 7.89/1.49      | sK6 != X1
% 7.89/1.49      | sK2 != X3 ),
% 7.89/1.49      inference(resolution_lifted,[status(thm)],[c_14,c_789]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_947,plain,
% 7.89/1.49      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 7.89/1.49      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 7.89/1.49      | v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))
% 7.89/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 7.89/1.49      | v2_struct_0(X0)
% 7.89/1.49      | ~ v2_pre_topc(X0)
% 7.89/1.49      | ~ l1_pre_topc(X0)
% 7.89/1.49      | ~ v1_funct_1(X1) ),
% 7.89/1.49      inference(unflattening,[status(thm)],[c_946]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2501,plain,
% 7.89/1.49      ( ~ sP0(X0_53,sK6,X0_54,sK2,sK5)
% 7.89/1.49      | ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53))
% 7.89/1.49      | v1_funct_2(k2_tmap_1(sK2,X0_53,X0_54,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_53))
% 7.89/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53))))
% 7.89/1.49      | v2_struct_0(X0_53)
% 7.89/1.49      | ~ v2_pre_topc(X0_53)
% 7.89/1.49      | ~ l1_pre_topc(X0_53)
% 7.89/1.49      | ~ v1_funct_1(X0_54) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_947]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3626,plain,
% 7.89/1.49      ( sP0(X0_53,sK6,X0_54,sK2,sK5) != iProver_top
% 7.89/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
% 7.89/1.49      | v1_funct_2(k2_tmap_1(sK2,X0_53,X0_54,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_53)) = iProver_top
% 7.89/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_53) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_53) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_53) != iProver_top
% 7.89/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_2501]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_7023,plain,
% 7.89/1.49      ( sP0(X0_53,sK6,X0_54,sK2,sK5) != iProver_top
% 7.89/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
% 7.89/1.49      | v1_funct_2(k2_tmap_1(sK2,X0_53,X0_54,sK2),u1_struct_0(sK2),u1_struct_0(X0_53)) = iProver_top
% 7.89/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_53) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_53) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_53) != iProver_top
% 7.89/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_2518,c_3626]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_7027,plain,
% 7.89/1.49      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.89/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
% 7.89/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.89/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.89/1.49      | v2_struct_0(sK3) = iProver_top
% 7.89/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.89/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_7023]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_15,plain,
% 7.89/1.49      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.89/1.49      | ~ sP0(X4,X3,X2,X1,X0)
% 7.89/1.49      | v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
% 7.89/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_916,plain,
% 7.89/1.49      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.89/1.49      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 7.89/1.49      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 7.89/1.49      | v2_struct_0(X6)
% 7.89/1.49      | ~ v2_pre_topc(X6)
% 7.89/1.49      | ~ l1_pre_topc(X6)
% 7.89/1.49      | ~ v1_funct_1(X5)
% 7.89/1.49      | v1_funct_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)))
% 7.89/1.49      | X5 != X2
% 7.89/1.49      | X6 != X0
% 7.89/1.49      | sK5 != X4
% 7.89/1.49      | sK6 != X1
% 7.89/1.49      | sK2 != X3 ),
% 7.89/1.49      inference(resolution_lifted,[status(thm)],[c_15,c_789]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_917,plain,
% 7.89/1.49      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 7.89/1.49      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 7.89/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 7.89/1.49      | v2_struct_0(X0)
% 7.89/1.49      | ~ v2_pre_topc(X0)
% 7.89/1.49      | ~ l1_pre_topc(X0)
% 7.89/1.49      | ~ v1_funct_1(X1)
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) ),
% 7.89/1.49      inference(unflattening,[status(thm)],[c_916]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2502,plain,
% 7.89/1.49      ( ~ sP0(X0_53,sK6,X0_54,sK2,sK5)
% 7.89/1.49      | ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53))
% 7.89/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53))))
% 7.89/1.49      | v2_struct_0(X0_53)
% 7.89/1.49      | ~ v2_pre_topc(X0_53)
% 7.89/1.49      | ~ l1_pre_topc(X0_53)
% 7.89/1.49      | ~ v1_funct_1(X0_54)
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,X0_53,X0_54,k1_tsep_1(sK2,sK5,sK6))) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_917]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3625,plain,
% 7.89/1.49      ( sP0(X0_53,sK6,X0_54,sK2,sK5) != iProver_top
% 7.89/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
% 7.89/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_53) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_53) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_53) != iProver_top
% 7.89/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,X0_53,X0_54,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_2502]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_6780,plain,
% 7.89/1.49      ( sP0(X0_53,sK6,X0_54,sK2,sK5) != iProver_top
% 7.89/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
% 7.89/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_53) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_53) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_53) != iProver_top
% 7.89/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,X0_53,X0_54,sK2)) = iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_2518,c_3625]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_6783,plain,
% 7.89/1.49      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.89/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.89/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.89/1.49      | v2_struct_0(sK3) = iProver_top
% 7.89/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top
% 7.89/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_6780]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2567,plain,
% 7.89/1.49      ( X0_54 != X1_54
% 7.89/1.49      | k2_tmap_1(X0_53,X1_53,X0_54,X2_53) = k2_tmap_1(X3_53,X4_53,X1_54,X5_53)
% 7.89/1.49      | X0_53 != X3_53
% 7.89/1.49      | X1_53 != X4_53
% 7.89/1.49      | X2_53 != X5_53 ),
% 7.89/1.49      theory(equality) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4114,plain,
% 7.89/1.49      ( X0_54 != X1_54
% 7.89/1.49      | k2_tmap_1(sK2,X0_53,X0_54,k1_tsep_1(sK2,sK5,sK6)) = k2_tmap_1(X1_53,X2_53,X1_54,X3_53)
% 7.89/1.49      | X0_53 != X2_53
% 7.89/1.49      | k1_tsep_1(sK2,sK5,sK6) != X3_53
% 7.89/1.49      | sK2 != X1_53 ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2567]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4787,plain,
% 7.89/1.49      ( X0_54 != X1_54
% 7.89/1.49      | k2_tmap_1(sK2,X0_53,X0_54,k1_tsep_1(sK2,sK5,sK6)) = k2_tmap_1(sK2,X1_53,X1_54,X2_53)
% 7.89/1.49      | X0_53 != X1_53
% 7.89/1.49      | k1_tsep_1(sK2,sK5,sK6) != X2_53
% 7.89/1.49      | sK2 != sK2 ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_4114]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_6512,plain,
% 7.89/1.49      ( X0_54 != X1_54
% 7.89/1.49      | k2_tmap_1(sK2,X0_53,X0_54,k1_tsep_1(sK2,sK5,sK6)) = k2_tmap_1(sK2,X1_53,X1_54,sK2)
% 7.89/1.49      | X0_53 != X1_53
% 7.89/1.49      | k1_tsep_1(sK2,sK5,sK6) != sK2
% 7.89/1.49      | sK2 != sK2 ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_4787]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_6513,plain,
% 7.89/1.49      ( k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)) = k2_tmap_1(sK2,sK3,sK4,sK2)
% 7.89/1.49      | sK4 != sK4
% 7.89/1.49      | k1_tsep_1(sK2,sK5,sK6) != sK2
% 7.89/1.49      | sK3 != sK3
% 7.89/1.49      | sK2 != sK2 ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_6512]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2557,plain,
% 7.89/1.49      ( X0_53 != X1_53 | X2_53 != X1_53 | X2_53 = X0_53 ),
% 7.89/1.49      theory(equality) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4986,plain,
% 7.89/1.49      ( X0_53 != X1_53 | X1_53 = X0_53 ),
% 7.89/1.49      inference(resolution,[status(thm)],[c_2557,c_2552]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_5663,plain,
% 7.89/1.49      ( sK2 = k1_tsep_1(sK2,sK5,sK6) ),
% 7.89/1.49      inference(resolution,[status(thm)],[c_4986,c_2518]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_17,plain,
% 7.89/1.49      ( sP0(X0,X1,X2,X3,X4)
% 7.89/1.49      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
% 7.89/1.49      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
% 7.89/1.49      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
% 7.89/1.49      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
% 7.89/1.49      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 7.89/1.49      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
% 7.89/1.49      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
% 7.89/1.49      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
% 7.89/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2538,plain,
% 7.89/1.49      ( sP0(X0_53,X1_53,X0_54,X2_53,X3_53)
% 7.89/1.49      | ~ v5_pre_topc(k2_tmap_1(X2_53,X0_53,X0_54,X1_53),X1_53,X0_53)
% 7.89/1.49      | ~ v5_pre_topc(k2_tmap_1(X2_53,X0_53,X0_54,X3_53),X3_53,X0_53)
% 7.89/1.49      | ~ v1_funct_2(k2_tmap_1(X2_53,X0_53,X0_54,X1_53),u1_struct_0(X1_53),u1_struct_0(X0_53))
% 7.89/1.49      | ~ v1_funct_2(k2_tmap_1(X2_53,X0_53,X0_54,X3_53),u1_struct_0(X3_53),u1_struct_0(X0_53))
% 7.89/1.49      | ~ m1_subset_1(k2_tmap_1(X2_53,X0_53,X0_54,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X0_53))))
% 7.89/1.49      | ~ m1_subset_1(k2_tmap_1(X2_53,X0_53,X0_54,X3_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X0_53))))
% 7.89/1.49      | ~ v1_funct_1(k2_tmap_1(X2_53,X0_53,X0_54,X1_53))
% 7.89/1.49      | ~ v1_funct_1(k2_tmap_1(X2_53,X0_53,X0_54,X3_53)) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_17]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4223,plain,
% 7.89/1.49      ( sP0(sK3,X0_53,sK4,sK2,sK5)
% 7.89/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_53),X0_53,sK3)
% 7.89/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.89/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_53),u1_struct_0(X0_53),u1_struct_0(sK3))
% 7.89/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.89/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK3))))
% 7.89/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.89/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_53))
% 7.89/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2538]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_5043,plain,
% 7.89/1.49      ( sP0(sK3,sK6,sK4,sK2,sK5)
% 7.89/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.89/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.89/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.89/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.89/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.89/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.89/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.89/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_4223]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_5044,plain,
% 7.89/1.49      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 7.89/1.49      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.89/1.49      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.89/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.89/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.89/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.89/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_5043]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2,plain,
% 7.89/1.49      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.89/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2548,plain,
% 7.89/1.49      ( ~ l1_pre_topc(X0_53) | l1_struct_0(X0_53) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4510,plain,
% 7.89/1.49      ( ~ l1_pre_topc(sK5) | l1_struct_0(sK5) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2548]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4511,plain,
% 7.89/1.49      ( l1_pre_topc(sK5) != iProver_top
% 7.89/1.49      | l1_struct_0(sK5) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_4510]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4507,plain,
% 7.89/1.49      ( ~ l1_pre_topc(sK6) | l1_struct_0(sK6) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2548]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4508,plain,
% 7.89/1.49      ( l1_pre_topc(sK6) != iProver_top
% 7.89/1.49      | l1_struct_0(sK6) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_4507]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_6,plain,
% 7.89/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.89/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.89/1.49      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 7.89/1.49      | ~ l1_struct_0(X3)
% 7.89/1.49      | ~ l1_struct_0(X2)
% 7.89/1.49      | ~ l1_struct_0(X1)
% 7.89/1.49      | ~ v1_funct_1(X0) ),
% 7.89/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2544,plain,
% 7.89/1.49      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 7.89/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 7.89/1.49      | m1_subset_1(k2_tmap_1(X0_53,X1_53,X0_54,X2_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
% 7.89/1.49      | ~ l1_struct_0(X2_53)
% 7.89/1.49      | ~ l1_struct_0(X1_53)
% 7.89/1.49      | ~ l1_struct_0(X0_53)
% 7.89/1.49      | ~ v1_funct_1(X0_54) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3866,plain,
% 7.89/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.89/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK3))))
% 7.89/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.89/1.49      | ~ l1_struct_0(X0_53)
% 7.89/1.49      | ~ l1_struct_0(sK3)
% 7.89/1.49      | ~ l1_struct_0(sK2)
% 7.89/1.49      | ~ v1_funct_1(sK4) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2544]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4492,plain,
% 7.89/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.89/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.89/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.89/1.49      | ~ l1_struct_0(sK5)
% 7.89/1.49      | ~ l1_struct_0(sK3)
% 7.89/1.49      | ~ l1_struct_0(sK2)
% 7.89/1.49      | ~ v1_funct_1(sK4) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_3866]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4493,plain,
% 7.89/1.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.89/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top
% 7.89/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.89/1.49      | l1_struct_0(sK5) != iProver_top
% 7.89/1.49      | l1_struct_0(sK3) != iProver_top
% 7.89/1.49      | l1_struct_0(sK2) != iProver_top
% 7.89/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_4492]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_36,negated_conjecture,
% 7.89/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.89/1.49      | v5_pre_topc(sK4,sK2,sK3) ),
% 7.89/1.49      inference(cnf_transformation,[],[f124]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2525,negated_conjecture,
% 7.89/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.89/1.49      | v5_pre_topc(sK4,sK2,sK3) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_36]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3603,plain,
% 7.89/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
% 7.89/1.49      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_2525]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_86,plain,
% 7.89/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_69]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_89,plain,
% 7.89/1.49      ( v2_struct_0(sK6) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_66]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_90,plain,
% 7.89/1.49      ( m1_pre_topc(sK6,sK2) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_65]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_118,plain,
% 7.89/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
% 7.89/1.49      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_9,plain,
% 7.89/1.49      ( ~ v5_pre_topc(X0,X1,X2)
% 7.89/1.49      | v5_pre_topc(k2_tmap_1(X1,X2,X0,X3),X3,X2)
% 7.89/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.89/1.49      | ~ m1_pre_topc(X3,X1)
% 7.89/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.89/1.49      | v2_struct_0(X1)
% 7.89/1.49      | v2_struct_0(X2)
% 7.89/1.49      | v2_struct_0(X3)
% 7.89/1.49      | ~ v2_pre_topc(X2)
% 7.89/1.49      | ~ v2_pre_topc(X1)
% 7.89/1.49      | ~ l1_pre_topc(X1)
% 7.89/1.49      | ~ l1_pre_topc(X2)
% 7.89/1.49      | ~ v1_funct_1(X0) ),
% 7.89/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2541,plain,
% 7.89/1.49      ( ~ v5_pre_topc(X0_54,X0_53,X1_53)
% 7.89/1.49      | v5_pre_topc(k2_tmap_1(X0_53,X1_53,X0_54,X2_53),X2_53,X1_53)
% 7.89/1.49      | ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 7.89/1.49      | ~ m1_pre_topc(X2_53,X0_53)
% 7.89/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 7.89/1.49      | v2_struct_0(X0_53)
% 7.89/1.49      | v2_struct_0(X1_53)
% 7.89/1.49      | v2_struct_0(X2_53)
% 7.89/1.49      | ~ v2_pre_topc(X0_53)
% 7.89/1.49      | ~ v2_pre_topc(X1_53)
% 7.89/1.49      | ~ l1_pre_topc(X0_53)
% 7.89/1.49      | ~ l1_pre_topc(X1_53)
% 7.89/1.49      | ~ v1_funct_1(X0_54) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_9]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3911,plain,
% 7.89/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_53),X0_53,sK3)
% 7.89/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.89/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.89/1.49      | ~ m1_pre_topc(X0_53,sK2)
% 7.89/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.89/1.49      | v2_struct_0(X0_53)
% 7.89/1.49      | v2_struct_0(sK3)
% 7.89/1.49      | v2_struct_0(sK2)
% 7.89/1.49      | ~ v2_pre_topc(sK3)
% 7.89/1.49      | ~ v2_pre_topc(sK2)
% 7.89/1.49      | ~ l1_pre_topc(sK3)
% 7.89/1.49      | ~ l1_pre_topc(sK2)
% 7.89/1.49      | ~ v1_funct_1(sK4) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2541]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4029,plain,
% 7.89/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.89/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.89/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.89/1.49      | ~ m1_pre_topc(sK6,sK2)
% 7.89/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.89/1.49      | v2_struct_0(sK6)
% 7.89/1.49      | v2_struct_0(sK3)
% 7.89/1.49      | v2_struct_0(sK2)
% 7.89/1.49      | ~ v2_pre_topc(sK3)
% 7.89/1.49      | ~ v2_pre_topc(sK2)
% 7.89/1.49      | ~ l1_pre_topc(sK3)
% 7.89/1.49      | ~ l1_pre_topc(sK2)
% 7.89/1.49      | ~ v1_funct_1(sK4) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_3911]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4030,plain,
% 7.89/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
% 7.89/1.49      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.89/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.89/1.49      | m1_pre_topc(sK6,sK2) != iProver_top
% 7.89/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.89/1.49      | v2_struct_0(sK6) = iProver_top
% 7.89/1.49      | v2_struct_0(sK3) = iProver_top
% 7.89/1.49      | v2_struct_0(sK2) = iProver_top
% 7.89/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.89/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.89/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_4029]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4443,plain,
% 7.89/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_3603,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,
% 7.89/1.49                 c_89,c_90,c_118,c_4030]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4445,plain,
% 7.89/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
% 7.89/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_4443]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2515,negated_conjecture,
% 7.89/1.49      ( m1_pre_topc(sK5,sK2) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_67]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3612,plain,
% 7.89/1.49      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_2515]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3581,plain,
% 7.89/1.49      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 7.89/1.49      | l1_pre_topc(X1_53) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_53) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_2547]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4438,plain,
% 7.89/1.49      ( l1_pre_topc(sK5) = iProver_top
% 7.89/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_3612,c_3581]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4441,plain,
% 7.89/1.49      ( l1_pre_topc(sK5) | ~ l1_pre_topc(sK2) ),
% 7.89/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_4438]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2517,negated_conjecture,
% 7.89/1.49      ( m1_pre_topc(sK6,sK2) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_65]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3610,plain,
% 7.89/1.49      ( m1_pre_topc(sK6,sK2) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_2517]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4437,plain,
% 7.89/1.49      ( l1_pre_topc(sK6) = iProver_top
% 7.89/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_3610,c_3581]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4440,plain,
% 7.89/1.49      ( l1_pre_topc(sK6) | ~ l1_pre_topc(sK2) ),
% 7.89/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_4437]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4408,plain,
% 7.89/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.89/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.89/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.89/1.49      | ~ l1_struct_0(sK6)
% 7.89/1.49      | ~ l1_struct_0(sK3)
% 7.89/1.49      | ~ l1_struct_0(sK2)
% 7.89/1.49      | ~ v1_funct_1(sK4) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_3866]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4409,plain,
% 7.89/1.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.89/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top
% 7.89/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.89/1.49      | l1_struct_0(sK6) != iProver_top
% 7.89/1.49      | l1_struct_0(sK3) != iProver_top
% 7.89/1.49      | l1_struct_0(sK2) != iProver_top
% 7.89/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_4408]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_60,negated_conjecture,
% 7.89/1.49      ( v5_pre_topc(sK4,sK2,sK3)
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
% 7.89/1.49      inference(cnf_transformation,[],[f100]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2519,negated_conjecture,
% 7.89/1.49      ( v5_pre_topc(sK4,sK2,sK3)
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_60]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3609,plain,
% 7.89/1.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_2519]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_87,plain,
% 7.89/1.49      ( v2_struct_0(sK5) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_68]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_88,plain,
% 7.89/1.49      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_67]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_94,plain,
% 7.89/1.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_11,plain,
% 7.89/1.49      ( ~ v5_pre_topc(X0,X1,X2)
% 7.89/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.89/1.49      | ~ m1_pre_topc(X3,X1)
% 7.89/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.89/1.49      | v2_struct_0(X1)
% 7.89/1.49      | v2_struct_0(X2)
% 7.89/1.49      | v2_struct_0(X3)
% 7.89/1.49      | ~ v2_pre_topc(X2)
% 7.89/1.49      | ~ v2_pre_topc(X1)
% 7.89/1.49      | ~ l1_pre_topc(X1)
% 7.89/1.49      | ~ l1_pre_topc(X2)
% 7.89/1.49      | ~ v1_funct_1(X0)
% 7.89/1.49      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 7.89/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2539,plain,
% 7.89/1.49      ( ~ v5_pre_topc(X0_54,X0_53,X1_53)
% 7.89/1.49      | ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 7.89/1.49      | ~ m1_pre_topc(X2_53,X0_53)
% 7.89/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 7.89/1.49      | v2_struct_0(X0_53)
% 7.89/1.49      | v2_struct_0(X1_53)
% 7.89/1.49      | v2_struct_0(X2_53)
% 7.89/1.49      | ~ v2_pre_topc(X0_53)
% 7.89/1.49      | ~ v2_pre_topc(X1_53)
% 7.89/1.49      | ~ l1_pre_topc(X0_53)
% 7.89/1.49      | ~ l1_pre_topc(X1_53)
% 7.89/1.49      | ~ v1_funct_1(X0_54)
% 7.89/1.49      | v1_funct_1(k2_tmap_1(X0_53,X1_53,X0_54,X2_53)) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_11]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3871,plain,
% 7.89/1.49      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 7.89/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.89/1.49      | ~ m1_pre_topc(X0_53,sK2)
% 7.89/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.89/1.49      | v2_struct_0(X0_53)
% 7.89/1.49      | v2_struct_0(sK3)
% 7.89/1.49      | v2_struct_0(sK2)
% 7.89/1.49      | ~ v2_pre_topc(sK3)
% 7.89/1.49      | ~ v2_pre_topc(sK2)
% 7.89/1.49      | ~ l1_pre_topc(sK3)
% 7.89/1.49      | ~ l1_pre_topc(sK2)
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_53))
% 7.89/1.49      | ~ v1_funct_1(sK4) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2539]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3992,plain,
% 7.89/1.49      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 7.89/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.89/1.49      | ~ m1_pre_topc(sK5,sK2)
% 7.89/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.89/1.49      | v2_struct_0(sK5)
% 7.89/1.49      | v2_struct_0(sK3)
% 7.89/1.49      | v2_struct_0(sK2)
% 7.89/1.49      | ~ v2_pre_topc(sK3)
% 7.89/1.49      | ~ v2_pre_topc(sK2)
% 7.89/1.49      | ~ l1_pre_topc(sK3)
% 7.89/1.49      | ~ l1_pre_topc(sK2)
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.89/1.49      | ~ v1_funct_1(sK4) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_3871]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3993,plain,
% 7.89/1.49      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.89/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.89/1.49      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.89/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.89/1.49      | v2_struct_0(sK5) = iProver_top
% 7.89/1.49      | v2_struct_0(sK3) = iProver_top
% 7.89/1.49      | v2_struct_0(sK2) = iProver_top
% 7.89/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.89/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top
% 7.89/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_3992]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4247,plain,
% 7.89/1.49      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_3609,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,
% 7.89/1.49                 c_87,c_88,c_94,c_3993]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4249,plain,
% 7.89/1.49      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
% 7.89/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_4247]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_44,negated_conjecture,
% 7.89/1.49      ( v5_pre_topc(sK4,sK2,sK3)
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 7.89/1.49      inference(cnf_transformation,[],[f116]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2523,negated_conjecture,
% 7.89/1.49      ( v5_pre_topc(sK4,sK2,sK3)
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_44]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3605,plain,
% 7.89/1.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_2523]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_110,plain,
% 7.89/1.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3989,plain,
% 7.89/1.49      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 7.89/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.89/1.49      | ~ m1_pre_topc(sK6,sK2)
% 7.89/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.89/1.49      | v2_struct_0(sK6)
% 7.89/1.49      | v2_struct_0(sK3)
% 7.89/1.49      | v2_struct_0(sK2)
% 7.89/1.49      | ~ v2_pre_topc(sK3)
% 7.89/1.49      | ~ v2_pre_topc(sK2)
% 7.89/1.49      | ~ l1_pre_topc(sK3)
% 7.89/1.49      | ~ l1_pre_topc(sK2)
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 7.89/1.49      | ~ v1_funct_1(sK4) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_3871]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3990,plain,
% 7.89/1.49      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.89/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.89/1.49      | m1_pre_topc(sK6,sK2) != iProver_top
% 7.89/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.89/1.49      | v2_struct_0(sK6) = iProver_top
% 7.89/1.49      | v2_struct_0(sK3) = iProver_top
% 7.89/1.49      | v2_struct_0(sK2) = iProver_top
% 7.89/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.89/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.89/1.49      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top
% 7.89/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_3989]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4242,plain,
% 7.89/1.49      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_3605,c_78,c_79,c_80,c_81,c_82,c_83,c_84,c_85,c_86,
% 7.89/1.49                 c_89,c_90,c_110,c_3990]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4244,plain,
% 7.89/1.49      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 7.89/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_4242]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_30,negated_conjecture,
% 7.89/1.49      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.89/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.89/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.89/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.89/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.89/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.89/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.89/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.89/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.89/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.89/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 7.89/1.49      | ~ v1_funct_1(sK4) ),
% 7.89/1.49      inference(cnf_transformation,[],[f130]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_500,plain,
% 7.89/1.49      ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 7.89/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.89/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.89/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.89/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.89/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.89/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.89/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.89/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_30,c_71,c_70,c_69]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_501,negated_conjecture,
% 7.89/1.49      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.89/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.89/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.89/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.89/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.89/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.89/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.89/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.89/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 7.89/1.49      inference(renaming,[status(thm)],[c_500]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2504,negated_conjecture,
% 7.89/1.49      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.89/1.49      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.89/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.89/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.89/1.49      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.89/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.89/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.89/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.89/1.49      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_501]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_10,plain,
% 7.89/1.49      ( ~ v5_pre_topc(X0,X1,X2)
% 7.89/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.89/1.49      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 7.89/1.49      | ~ m1_pre_topc(X3,X1)
% 7.89/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.89/1.49      | v2_struct_0(X1)
% 7.89/1.49      | v2_struct_0(X2)
% 7.89/1.49      | v2_struct_0(X3)
% 7.89/1.49      | ~ v2_pre_topc(X2)
% 7.89/1.49      | ~ v2_pre_topc(X1)
% 7.89/1.49      | ~ l1_pre_topc(X1)
% 7.89/1.49      | ~ l1_pre_topc(X2)
% 7.89/1.49      | ~ v1_funct_1(X0) ),
% 7.89/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2540,plain,
% 7.89/1.49      ( ~ v5_pre_topc(X0_54,X0_53,X1_53)
% 7.89/1.49      | ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 7.89/1.49      | v1_funct_2(k2_tmap_1(X0_53,X1_53,X0_54,X2_53),u1_struct_0(X2_53),u1_struct_0(X1_53))
% 7.89/1.49      | ~ m1_pre_topc(X2_53,X0_53)
% 7.89/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 7.89/1.49      | v2_struct_0(X0_53)
% 7.89/1.49      | v2_struct_0(X1_53)
% 7.89/1.49      | v2_struct_0(X2_53)
% 7.89/1.49      | ~ v2_pre_topc(X0_53)
% 7.89/1.49      | ~ v2_pre_topc(X1_53)
% 7.89/1.49      | ~ l1_pre_topc(X0_53)
% 7.89/1.49      | ~ l1_pre_topc(X1_53)
% 7.89/1.49      | ~ v1_funct_1(X0_54) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_10]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3906,plain,
% 7.89/1.49      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 7.89/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_53),u1_struct_0(X0_53),u1_struct_0(sK3))
% 7.89/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.89/1.49      | ~ m1_pre_topc(X0_53,sK2)
% 7.89/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.89/1.49      | v2_struct_0(X0_53)
% 7.89/1.49      | v2_struct_0(sK3)
% 7.89/1.49      | v2_struct_0(sK2)
% 7.89/1.49      | ~ v2_pre_topc(sK3)
% 7.89/1.49      | ~ v2_pre_topc(sK2)
% 7.89/1.49      | ~ l1_pre_topc(sK3)
% 7.89/1.49      | ~ l1_pre_topc(sK2)
% 7.89/1.49      | ~ v1_funct_1(sK4) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2540]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4019,plain,
% 7.89/1.49      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 7.89/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.89/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.89/1.49      | ~ m1_pre_topc(sK6,sK2)
% 7.89/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.89/1.49      | v2_struct_0(sK6)
% 7.89/1.49      | v2_struct_0(sK3)
% 7.89/1.49      | v2_struct_0(sK2)
% 7.89/1.49      | ~ v2_pre_topc(sK3)
% 7.89/1.49      | ~ v2_pre_topc(sK2)
% 7.89/1.49      | ~ l1_pre_topc(sK3)
% 7.89/1.49      | ~ l1_pre_topc(sK2)
% 7.89/1.49      | ~ v1_funct_1(sK4) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_3906]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4022,plain,
% 7.89/1.49      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 7.89/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.89/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.89/1.49      | ~ m1_pre_topc(sK5,sK2)
% 7.89/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.89/1.49      | v2_struct_0(sK5)
% 7.89/1.49      | v2_struct_0(sK3)
% 7.89/1.49      | v2_struct_0(sK2)
% 7.89/1.49      | ~ v2_pre_topc(sK3)
% 7.89/1.49      | ~ v2_pre_topc(sK2)
% 7.89/1.49      | ~ l1_pre_topc(sK3)
% 7.89/1.49      | ~ l1_pre_topc(sK2)
% 7.89/1.49      | ~ v1_funct_1(sK4) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_3906]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4032,plain,
% 7.89/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.89/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.89/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.89/1.49      | ~ m1_pre_topc(sK5,sK2)
% 7.89/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.89/1.49      | v2_struct_0(sK5)
% 7.89/1.49      | v2_struct_0(sK3)
% 7.89/1.49      | v2_struct_0(sK2)
% 7.89/1.49      | ~ v2_pre_topc(sK3)
% 7.89/1.49      | ~ v2_pre_topc(sK2)
% 7.89/1.49      | ~ l1_pre_topc(sK3)
% 7.89/1.49      | ~ l1_pre_topc(sK2)
% 7.89/1.49      | ~ v1_funct_1(sK4) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_3911]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4073,negated_conjecture,
% 7.89/1.49      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 7.89/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.89/1.49      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_2504,c_77,c_76,c_75,c_74,c_73,c_72,c_71,c_70,c_69,
% 7.89/1.49                 c_68,c_67,c_66,c_65,c_30,c_3989,c_3992,c_4019,c_4022,
% 7.89/1.49                 c_4029,c_4032]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4075,plain,
% 7.89/1.49      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.89/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.89/1.49      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_4073]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4002,plain,
% 7.89/1.49      ( m1_pre_topc(sK2,sK2) = iProver_top
% 7.89/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_3999]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3972,plain,
% 7.89/1.49      ( sK2 = sK2 ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2552]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3938,plain,
% 7.89/1.49      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2548]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3939,plain,
% 7.89/1.49      ( l1_pre_topc(sK2) != iProver_top
% 7.89/1.49      | l1_struct_0(sK2) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_3938]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_13,plain,
% 7.89/1.49      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.89/1.49      | ~ sP0(X4,X3,X2,X1,X0)
% 7.89/1.49      | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) ),
% 7.89/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_976,plain,
% 7.89/1.49      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.89/1.49      | v5_pre_topc(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_tsep_1(X3,X4,X1),X0)
% 7.89/1.49      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 7.89/1.49      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 7.89/1.49      | v2_struct_0(X6)
% 7.89/1.49      | ~ v2_pre_topc(X6)
% 7.89/1.49      | ~ l1_pre_topc(X6)
% 7.89/1.49      | ~ v1_funct_1(X5)
% 7.89/1.49      | X5 != X2
% 7.89/1.49      | X6 != X0
% 7.89/1.49      | sK5 != X4
% 7.89/1.49      | sK6 != X1
% 7.89/1.49      | sK2 != X3 ),
% 7.89/1.49      inference(resolution_lifted,[status(thm)],[c_13,c_789]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_977,plain,
% 7.89/1.49      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 7.89/1.49      | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
% 7.89/1.49      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 7.89/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 7.89/1.49      | v2_struct_0(X0)
% 7.89/1.49      | ~ v2_pre_topc(X0)
% 7.89/1.49      | ~ l1_pre_topc(X0)
% 7.89/1.49      | ~ v1_funct_1(X1) ),
% 7.89/1.49      inference(unflattening,[status(thm)],[c_976]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2500,plain,
% 7.89/1.49      ( ~ sP0(X0_53,sK6,X0_54,sK2,sK5)
% 7.89/1.49      | v5_pre_topc(k2_tmap_1(sK2,X0_53,X0_54,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_53)
% 7.89/1.49      | ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53))
% 7.89/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53))))
% 7.89/1.49      | v2_struct_0(X0_53)
% 7.89/1.49      | ~ v2_pre_topc(X0_53)
% 7.89/1.49      | ~ l1_pre_topc(X0_53)
% 7.89/1.49      | ~ v1_funct_1(X0_54) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_977]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2683,plain,
% 7.89/1.49      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 7.89/1.49      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
% 7.89/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.89/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.89/1.49      | v2_struct_0(sK3)
% 7.89/1.49      | ~ v2_pre_topc(sK3)
% 7.89/1.49      | ~ l1_pre_topc(sK3)
% 7.89/1.49      | ~ v1_funct_1(sK4) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2500]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2553,plain,( X0_54 = X0_54 ),theory(equality) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2593,plain,
% 7.89/1.49      ( sK4 = sK4 ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2553]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2592,plain,
% 7.89/1.49      ( sK3 = sK3 ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2552]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_194,plain,
% 7.89/1.49      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_196,plain,
% 7.89/1.49      ( l1_pre_topc(sK3) != iProver_top
% 7.89/1.49      | l1_struct_0(sK3) = iProver_top ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_194]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_195,plain,
% 7.89/1.49      ( ~ l1_pre_topc(sK3) | l1_struct_0(sK3) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_40,negated_conjecture,
% 7.89/1.49      ( v5_pre_topc(sK4,sK2,sK3)
% 7.89/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
% 7.89/1.49      inference(cnf_transformation,[],[f120]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_114,plain,
% 7.89/1.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.89/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_52,negated_conjecture,
% 7.89/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.89/1.49      | v5_pre_topc(sK4,sK2,sK3) ),
% 7.89/1.49      inference(cnf_transformation,[],[f108]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_102,plain,
% 7.89/1.49      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
% 7.89/1.49      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_56,negated_conjecture,
% 7.89/1.49      ( v5_pre_topc(sK4,sK2,sK3)
% 7.89/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 7.89/1.49      inference(cnf_transformation,[],[f104]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_98,plain,
% 7.89/1.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.89/1.49      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(contradiction,plain,
% 7.89/1.49      ( $false ),
% 7.89/1.49      inference(minisat,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_23907,c_8565,c_8550,c_7702,c_7297,c_7169,c_7027,
% 7.89/1.49                 c_6783,c_6513,c_5663,c_5044,c_5043,c_4511,c_4510,c_4508,
% 7.89/1.49                 c_4507,c_4493,c_4492,c_4445,c_4443,c_4441,c_4438,c_4440,
% 7.89/1.49                 c_4437,c_4409,c_4408,c_4249,c_4247,c_4244,c_4242,c_4075,
% 7.89/1.49                 c_4073,c_4002,c_3972,c_3939,c_3938,c_2683,c_2518,c_2593,
% 7.89/1.49                 c_2592,c_196,c_195,c_114,c_40,c_102,c_52,c_98,c_56,c_86,
% 7.89/1.49                 c_69,c_85,c_70,c_84,c_71,c_83,c_72,c_82,c_73,c_81,c_74,
% 7.89/1.49                 c_80,c_75,c_79,c_78]) ).
% 7.89/1.49  
% 7.89/1.49  
% 7.89/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.89/1.49  
% 7.89/1.49  ------                               Statistics
% 7.89/1.49  
% 7.89/1.49  ------ Selected
% 7.89/1.49  
% 7.89/1.49  total_time:                             0.972
% 7.89/1.49  
%------------------------------------------------------------------------------
