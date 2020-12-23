%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:18 EST 2020

% Result     : Theorem 7.94s
% Output     : CNFRefutation 7.94s
% Verified   : 
% Statistics : Number of formulae       :  306 (15434 expanded)
%              Number of clauses        :  214 (2680 expanded)
%              Number of leaves         :   18 (5702 expanded)
%              Depth                    :   31
%              Number of atoms          : 2112 (521687 expanded)
%              Number of equality atoms :  635 (19876 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal clause size      :   78 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f109,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f51])).

fof(f65,plain,(
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
    inference(flattening,[],[f64])).

fof(f70,plain,(
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

fof(f69,plain,(
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

fof(f68,plain,(
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

fof(f67,plain,(
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

fof(f66,plain,
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

fof(f71,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f65,f70,f69,f68,f67,f66])).

fof(f119,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f71])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f117,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f71])).

fof(f111,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f112,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f113,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f114,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f115,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f116,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f118,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f71])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
      <=> sP0(X1,X3,X4,X0,X2) )
      | ~ sP1(X2,X0,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f53])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f60,plain,(
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
    inference(rectify,[],[f59])).

fof(f91,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0)
      | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
      | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
      | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f14,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f52,plain,(
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

fof(f54,plain,(
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
    inference(definition_folding,[],[f41,f53,f52])).

fof(f105,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f125,plain,(
    r4_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f71])).

fof(f120,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f71])).

fof(f121,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f122,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f71])).

fof(f123,plain,(
    m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f124,plain,(
    k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f71])).

fof(f93,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f95,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f156,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f52])).

fof(f62,plain,(
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
    inference(flattening,[],[f61])).

fof(f63,plain,(
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
    inference(rectify,[],[f62])).

fof(f104,plain,(
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
    inference(cnf_transformation,[],[f63])).

fof(f144,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f148,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f152,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f140,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f128,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f132,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f136,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f102,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f13,axiom,(
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

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f103,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f99,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f158,plain,
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
    inference(cnf_transformation,[],[f71])).

cnf(c_37,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_4140,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_78,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_4126,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_78])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4158,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9534,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0)) = k2_tmap_1(sK2,sK3,sK4,X0)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4126,c_4158])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_4162,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8556,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k7_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4126,c_4162])).

cnf(c_80,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_4833,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4934,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_4833])).

cnf(c_9049,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8556,c_80,c_78,c_4934])).

cnf(c_9574,plain,
    ( k2_tmap_1(sK2,sK3,sK4,X0) = k7_relat_1(sK4,u1_struct_0(X0))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9534,c_9049])).

cnf(c_86,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_87,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_86])).

cnf(c_85,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_88,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_85])).

cnf(c_84,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_89,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_84])).

cnf(c_83,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_90,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_83])).

cnf(c_82,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_91,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_82])).

cnf(c_81,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_92,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_81])).

cnf(c_93,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_80])).

cnf(c_79,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_94,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_79])).

cnf(c_19622,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | k2_tmap_1(sK2,sK3,sK4,X0) = k7_relat_1(sK4,u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9574,c_87,c_88,c_89,c_90,c_91,c_92,c_93,c_94])).

cnf(c_19623,plain,
    ( k2_tmap_1(sK2,sK3,sK4,X0) = k7_relat_1(sK4,u1_struct_0(X0))
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_19622])).

cnf(c_19631,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2))
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4140,c_19623])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_998,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_8,c_7])).

cnf(c_4115,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_998])).

cnf(c_4891,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4126,c_4115])).

cnf(c_4892,plain,
    ( ~ v1_relat_1(sK4)
    | k7_relat_1(sK4,u1_struct_0(sK2)) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4891])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_4977,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5159,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_4977])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_672,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_673,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_672])).

cnf(c_794,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_673])).

cnf(c_4876,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_5245,plain,
    ( ~ r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4876])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_5855,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_6320,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4891,c_78,c_4892,c_5159,c_5245,c_5855])).

cnf(c_19668,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19631,c_6320])).

cnf(c_20897,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19668,c_89])).

cnf(c_23,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | sP0(X4,X3,X2,X1,X0)
    | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
    | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
    | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
    | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_33,plain,
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
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_72,negated_conjecture,
    ( r4_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1016,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ v1_funct_1(X2)
    | sK5 != X0
    | sK6 != X3
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_72])).

cnf(c_1017,plain,
    ( sP1(sK5,sK2,X0,sK6,X1)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK6,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_1016])).

cnf(c_77,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_76,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_75,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_74,negated_conjecture,
    ( m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1021,plain,
    ( ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | sP1(sK5,sK2,X0,sK6,X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1017,c_86,c_85,c_84,c_77,c_76,c_75,c_74])).

cnf(c_1022,plain,
    ( sP1(sK5,sK2,X0,sK6,X1)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_1021])).

cnf(c_1057,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_tsep_1(X3,X4,X1),X0)
    | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))))
    | v2_struct_0(X6)
    | ~ l1_pre_topc(X6)
    | ~ v2_pre_topc(X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)))
    | X5 != X2
    | X6 != X0
    | sK5 != X4
    | sK6 != X1
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_1022])).

cnf(c_1058,plain,
    ( sP0(X0,sK6,X1,sK2,sK5)
    | ~ v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(unflattening,[status(thm)],[c_1057])).

cnf(c_4114,plain,
    ( sP0(X0,sK6,X1,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0) != iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1058])).

cnf(c_73,negated_conjecture,
    ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f124])).

cnf(c_4598,plain,
    ( sP0(X0,sK6,X1,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0,X1,sK2),sK2,X0) != iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0,X1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4114,c_73])).

cnf(c_20943,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_20897,c_4598])).

cnf(c_20963,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20943,c_20897])).

cnf(c_95,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_78])).

cnf(c_21,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1126,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
    | v1_funct_2(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
    | v2_struct_0(X6)
    | ~ l1_pre_topc(X6)
    | ~ v2_pre_topc(X6)
    | ~ v1_funct_1(X5)
    | X5 != X2
    | X6 != X0
    | sK5 != X4
    | sK6 != X1
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1022])).

cnf(c_1127,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_1126])).

cnf(c_4112,plain,
    ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1127])).

cnf(c_4428,plain,
    ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4112,c_73])).

cnf(c_19,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1186,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
    | m1_subset_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))))
    | v2_struct_0(X6)
    | ~ l1_pre_topc(X6)
    | ~ v2_pre_topc(X6)
    | ~ v1_funct_1(X5)
    | X5 != X2
    | X6 != X0
    | sK5 != X4
    | sK6 != X1
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_1022])).

cnf(c_1187,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_1186])).

cnf(c_4110,plain,
    ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0)))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1187])).

cnf(c_4445,plain,
    ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4110,c_73])).

cnf(c_41,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f156])).

cnf(c_4138,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_24,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_4152,plain,
    ( sP0(X0,X1,X2,X3,X4) = iProver_top
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) != iProver_top
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) != iProver_top
    | v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) != iProver_top
    | v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_9376,plain,
    ( sP0(sK3,X0,sK4,sK2,sK6) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4138,c_4152])).

cnf(c_53,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_119,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_49,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_123,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_45,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_127,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_10562,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
    | sP0(sK3,X0,sK4,sK2,sK6) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9376,c_119,c_123,c_127])).

cnf(c_10563,plain,
    ( sP0(sK3,X0,sK4,sK2,sK6) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10562])).

cnf(c_10577,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | sP0(sK3,sK2,sK4,sK2,sK6) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4445,c_10563])).

cnf(c_20,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1156,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_tsep_1(X3,X4,X1),X0)
    | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
    | v2_struct_0(X6)
    | ~ l1_pre_topc(X6)
    | ~ v2_pre_topc(X6)
    | ~ v1_funct_1(X5)
    | X5 != X2
    | X6 != X0
    | sK5 != X4
    | sK6 != X1
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_1022])).

cnf(c_1157,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_1156])).

cnf(c_4111,plain,
    ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0) = iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1157])).

cnf(c_4411,plain,
    ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0,X1,sK2),sK2,X0) = iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4111,c_73])).

cnf(c_5507,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4126,c_4411])).

cnf(c_7087,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
    | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5507,c_90,c_91,c_92,c_93,c_94])).

cnf(c_7088,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_7087])).

cnf(c_57,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_4134,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_9377,plain,
    ( sP0(sK3,X0,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4134,c_4152])).

cnf(c_69,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_103,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_65,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_107,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65])).

cnf(c_61,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_111,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_10889,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
    | sP0(sK3,X0,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9377,c_103,c_107,c_111])).

cnf(c_10890,plain,
    ( sP0(sK3,X0,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10889])).

cnf(c_10902,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4138,c_10890])).

cnf(c_115,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_131,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_8015,plain,
    ( sP0(X0,sK6,sK4,sK2,X1)
    | ~ v5_pre_topc(k2_tmap_1(sK2,X0,sK4,X1),X1,X0)
    | ~ v5_pre_topc(k2_tmap_1(sK2,X0,sK4,sK6),sK6,X0)
    | ~ v1_funct_2(k2_tmap_1(sK2,X0,sK4,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k2_tmap_1(sK2,X0,sK4,sK6),u1_struct_0(sK6),u1_struct_0(X0))
    | ~ m1_subset_1(k2_tmap_1(sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k2_tmap_1(sK2,X0,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0))))
    | ~ v1_funct_1(k2_tmap_1(sK2,X0,sK4,X1))
    | ~ v1_funct_1(k2_tmap_1(sK2,X0,sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_10868,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_8015])).

cnf(c_10869,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10868])).

cnf(c_10968,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10902,c_103,c_107,c_111,c_115,c_119,c_123,c_127,c_131,c_10869])).

cnf(c_22,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1096,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
    | v2_struct_0(X6)
    | ~ l1_pre_topc(X6)
    | ~ v2_pre_topc(X6)
    | ~ v1_funct_1(X5)
    | v1_funct_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)))
    | X5 != X2
    | X6 != X0
    | sK5 != X4
    | sK6 != X1
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_1022])).

cnf(c_1097,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X1)
    | v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(unflattening,[status(thm)],[c_1096])).

cnf(c_4113,plain,
    ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1097])).

cnf(c_4394,plain,
    ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0,X1,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4113,c_73])).

cnf(c_5496,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4126,c_4394])).

cnf(c_7080,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top
    | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5496,c_90,c_91,c_92,c_93,c_94])).

cnf(c_7081,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7080])).

cnf(c_10984,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10968,c_7081])).

cnf(c_11255,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | sP0(sK3,sK2,sK4,sK2,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10577,c_90,c_91,c_92,c_93,c_94,c_95,c_103,c_107,c_111,c_115,c_119,c_123,c_127,c_131,c_7088,c_10869,c_10984])).

cnf(c_11256,plain,
    ( sP0(sK3,sK2,sK4,sK2,sK6) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11255])).

cnf(c_11263,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | sP0(sK3,sK2,sK4,sK2,sK6) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4428,c_11256])).

cnf(c_11387,plain,
    ( sP0(sK3,sK2,sK4,sK2,sK6) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11263,c_90,c_91,c_92,c_93,c_94,c_95,c_10968])).

cnf(c_26,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_4150,plain,
    ( sP0(X0,X1,X2,X3,X4) != iProver_top
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_11397,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_11387,c_4150])).

cnf(c_5263,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_5266,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5263])).

cnf(c_16,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(k2_tmap_1(X1,X2,X0,X3),X3,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_4866,plain,
    ( v5_pre_topc(k2_tmap_1(X0,X1,sK4,X2),X2,X1)
    | ~ v5_pre_topc(sK4,X0,X1)
    | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_4967,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4866])).

cnf(c_5932,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4967])).

cnf(c_5934,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5932])).

cnf(c_11539,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11397,c_87,c_88,c_89,c_90,c_91,c_92,c_93,c_94,c_95,c_5266,c_5934])).

cnf(c_20913,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20897,c_11539])).

cnf(c_27681,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20963,c_90,c_91,c_92,c_93,c_94,c_95,c_20913])).

cnf(c_25,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_4151,plain,
    ( sP0(X0,X1,X2,X3,X4) != iProver_top
    | m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_27686,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_27681,c_4151])).

cnf(c_4130,plain,
    ( m1_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_74])).

cnf(c_19632,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK6) = k7_relat_1(sK4,u1_struct_0(sK6)) ),
    inference(superposition,[status(thm)],[c_4130,c_19623])).

cnf(c_27713,plain,
    ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27686,c_19632])).

cnf(c_29,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_4147,plain,
    ( sP0(X0,X1,X2,X3,X4) != iProver_top
    | m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_27687,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_27681,c_4147])).

cnf(c_4128,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_76])).

cnf(c_19633,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK5) = k7_relat_1(sK4,u1_struct_0(sK5)) ),
    inference(superposition,[status(thm)],[c_4128,c_19623])).

cnf(c_27710,plain,
    ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27687,c_19633])).

cnf(c_19837,plain,
    ( sP0(sK3,X0,sK4,sK2,sK6) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19632,c_4152])).

cnf(c_19923,plain,
    ( sP0(sK3,X0,sK4,sK2,sK6) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
    | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19837,c_19632])).

cnf(c_4135,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_19711,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19632,c_4135])).

cnf(c_98,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_75])).

cnf(c_99,plain,
    ( m1_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_74])).

cnf(c_18,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4153,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | m1_pre_topc(X3,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9683,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4126,c_4153])).

cnf(c_10280,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9683,c_87,c_88,c_89,c_90,c_91,c_92,c_93,c_94])).

cnf(c_10281,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_10280])).

cnf(c_19843,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_19632,c_10281])).

cnf(c_20304,plain,
    ( v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19711,c_98,c_99,c_19843])).

cnf(c_4137,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_19710,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19632,c_4137])).

cnf(c_4155,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(k2_tmap_1(X1,X2,X0,X3),X3,X2) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | m1_pre_topc(X3,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10029,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4126,c_4155])).

cnf(c_10291,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10029,c_87,c_88,c_89,c_90,c_91,c_92,c_93,c_94])).

cnf(c_10292,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_10291])).

cnf(c_19842,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | v2_struct_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_19632,c_10292])).

cnf(c_20336,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19710,c_98,c_99,c_19842])).

cnf(c_4136,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_19709,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19632,c_4136])).

cnf(c_17,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4154,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2)) = iProver_top
    | m1_pre_topc(X3,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19836,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_19632,c_4154])).

cnf(c_20457,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19709,c_87,c_88,c_89,c_90,c_91,c_92,c_93,c_94,c_95,c_98,c_99,c_19836])).

cnf(c_21228,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
    | sP0(sK3,X0,sK4,sK2,sK6) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19923,c_87,c_88,c_89,c_90,c_91,c_92,c_93,c_94,c_95,c_98,c_99,c_19709,c_19710,c_19711,c_19836,c_19842,c_19843])).

cnf(c_21229,plain,
    ( sP0(sK3,X0,sK4,sK2,sK6) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_21228])).

cnf(c_21243,plain,
    ( sP0(sK3,sK5,sK4,sK2,sK6) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19633,c_21229])).

cnf(c_21264,plain,
    ( sP0(sK3,sK5,sK4,sK2,sK6) = iProver_top
    | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) != iProver_top
    | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK5))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21243,c_19633])).

cnf(c_39,negated_conjecture,
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
    inference(cnf_transformation,[],[f158])).

cnf(c_546,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39,c_80,c_79,c_78])).

cnf(c_547,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(renaming,[status(thm)],[c_546])).

cnf(c_4117,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_19712,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19632,c_4117])).

cnf(c_96,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_77])).

cnf(c_97,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_76])).

cnf(c_4861,plain,
    ( ~ v5_pre_topc(sK4,X0,X1)
    | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k2_tmap_1(X0,X1,sK4,X2))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_4962,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4861])).

cnf(c_5046,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4962])).

cnf(c_5047,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5046])).

cnf(c_5314,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4967])).

cnf(c_5315,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5314])).

cnf(c_4871,plain,
    ( ~ v5_pre_topc(sK4,X0,X1)
    | v1_funct_2(k2_tmap_1(X0,X1,sK4,X2),u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_4972,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4871])).

cnf(c_5851,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4972])).

cnf(c_5852,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5851])).

cnf(c_20248,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19712,c_87,c_88,c_89,c_90,c_91,c_92,c_93,c_94,c_95,c_96,c_97,c_98,c_99,c_5047,c_5315,c_5852,c_19709,c_19710,c_19711,c_19836,c_19842,c_19843])).

cnf(c_20252,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20248,c_19633])).

cnf(c_21422,plain,
    ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21264,c_20252,c_20913])).

cnf(c_21423,plain,
    ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_21422])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27713,c_27710,c_21423])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:40:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 7.94/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.94/1.51  
% 7.94/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.94/1.51  
% 7.94/1.51  ------  iProver source info
% 7.94/1.51  
% 7.94/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.94/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.94/1.51  git: non_committed_changes: false
% 7.94/1.51  git: last_make_outside_of_git: false
% 7.94/1.51  
% 7.94/1.51  ------ 
% 7.94/1.51  
% 7.94/1.51  ------ Input Options
% 7.94/1.51  
% 7.94/1.51  --out_options                           all
% 7.94/1.51  --tptp_safe_out                         true
% 7.94/1.51  --problem_path                          ""
% 7.94/1.51  --include_path                          ""
% 7.94/1.51  --clausifier                            res/vclausify_rel
% 7.94/1.51  --clausifier_options                    --mode clausify
% 7.94/1.51  --stdin                                 false
% 7.94/1.51  --stats_out                             all
% 7.94/1.51  
% 7.94/1.51  ------ General Options
% 7.94/1.51  
% 7.94/1.51  --fof                                   false
% 7.94/1.51  --time_out_real                         305.
% 7.94/1.51  --time_out_virtual                      -1.
% 7.94/1.51  --symbol_type_check                     false
% 7.94/1.51  --clausify_out                          false
% 7.94/1.51  --sig_cnt_out                           false
% 7.94/1.51  --trig_cnt_out                          false
% 7.94/1.51  --trig_cnt_out_tolerance                1.
% 7.94/1.51  --trig_cnt_out_sk_spl                   false
% 7.94/1.51  --abstr_cl_out                          false
% 7.94/1.51  
% 7.94/1.51  ------ Global Options
% 7.94/1.51  
% 7.94/1.51  --schedule                              default
% 7.94/1.51  --add_important_lit                     false
% 7.94/1.51  --prop_solver_per_cl                    1000
% 7.94/1.51  --min_unsat_core                        false
% 7.94/1.51  --soft_assumptions                      false
% 7.94/1.51  --soft_lemma_size                       3
% 7.94/1.51  --prop_impl_unit_size                   0
% 7.94/1.51  --prop_impl_unit                        []
% 7.94/1.51  --share_sel_clauses                     true
% 7.94/1.51  --reset_solvers                         false
% 7.94/1.51  --bc_imp_inh                            [conj_cone]
% 7.94/1.51  --conj_cone_tolerance                   3.
% 7.94/1.51  --extra_neg_conj                        none
% 7.94/1.51  --large_theory_mode                     true
% 7.94/1.51  --prolific_symb_bound                   200
% 7.94/1.51  --lt_threshold                          2000
% 7.94/1.51  --clause_weak_htbl                      true
% 7.94/1.51  --gc_record_bc_elim                     false
% 7.94/1.51  
% 7.94/1.51  ------ Preprocessing Options
% 7.94/1.51  
% 7.94/1.51  --preprocessing_flag                    true
% 7.94/1.51  --time_out_prep_mult                    0.1
% 7.94/1.51  --splitting_mode                        input
% 7.94/1.51  --splitting_grd                         true
% 7.94/1.51  --splitting_cvd                         false
% 7.94/1.51  --splitting_cvd_svl                     false
% 7.94/1.51  --splitting_nvd                         32
% 7.94/1.51  --sub_typing                            true
% 7.94/1.51  --prep_gs_sim                           true
% 7.94/1.51  --prep_unflatten                        true
% 7.94/1.51  --prep_res_sim                          true
% 7.94/1.51  --prep_upred                            true
% 7.94/1.51  --prep_sem_filter                       exhaustive
% 7.94/1.51  --prep_sem_filter_out                   false
% 7.94/1.51  --pred_elim                             true
% 7.94/1.51  --res_sim_input                         true
% 7.94/1.51  --eq_ax_congr_red                       true
% 7.94/1.51  --pure_diseq_elim                       true
% 7.94/1.51  --brand_transform                       false
% 7.94/1.51  --non_eq_to_eq                          false
% 7.94/1.51  --prep_def_merge                        true
% 7.94/1.51  --prep_def_merge_prop_impl              false
% 7.94/1.51  --prep_def_merge_mbd                    true
% 7.94/1.51  --prep_def_merge_tr_red                 false
% 7.94/1.51  --prep_def_merge_tr_cl                  false
% 7.94/1.51  --smt_preprocessing                     true
% 7.94/1.51  --smt_ac_axioms                         fast
% 7.94/1.51  --preprocessed_out                      false
% 7.94/1.51  --preprocessed_stats                    false
% 7.94/1.51  
% 7.94/1.51  ------ Abstraction refinement Options
% 7.94/1.51  
% 7.94/1.51  --abstr_ref                             []
% 7.94/1.51  --abstr_ref_prep                        false
% 7.94/1.51  --abstr_ref_until_sat                   false
% 7.94/1.51  --abstr_ref_sig_restrict                funpre
% 7.94/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.94/1.51  --abstr_ref_under                       []
% 7.94/1.51  
% 7.94/1.51  ------ SAT Options
% 7.94/1.51  
% 7.94/1.51  --sat_mode                              false
% 7.94/1.51  --sat_fm_restart_options                ""
% 7.94/1.51  --sat_gr_def                            false
% 7.94/1.51  --sat_epr_types                         true
% 7.94/1.51  --sat_non_cyclic_types                  false
% 7.94/1.51  --sat_finite_models                     false
% 7.94/1.51  --sat_fm_lemmas                         false
% 7.94/1.51  --sat_fm_prep                           false
% 7.94/1.51  --sat_fm_uc_incr                        true
% 7.94/1.51  --sat_out_model                         small
% 7.94/1.51  --sat_out_clauses                       false
% 7.94/1.51  
% 7.94/1.51  ------ QBF Options
% 7.94/1.51  
% 7.94/1.51  --qbf_mode                              false
% 7.94/1.51  --qbf_elim_univ                         false
% 7.94/1.51  --qbf_dom_inst                          none
% 7.94/1.51  --qbf_dom_pre_inst                      false
% 7.94/1.51  --qbf_sk_in                             false
% 7.94/1.51  --qbf_pred_elim                         true
% 7.94/1.51  --qbf_split                             512
% 7.94/1.51  
% 7.94/1.51  ------ BMC1 Options
% 7.94/1.51  
% 7.94/1.51  --bmc1_incremental                      false
% 7.94/1.51  --bmc1_axioms                           reachable_all
% 7.94/1.51  --bmc1_min_bound                        0
% 7.94/1.51  --bmc1_max_bound                        -1
% 7.94/1.51  --bmc1_max_bound_default                -1
% 7.94/1.51  --bmc1_symbol_reachability              true
% 7.94/1.51  --bmc1_property_lemmas                  false
% 7.94/1.51  --bmc1_k_induction                      false
% 7.94/1.51  --bmc1_non_equiv_states                 false
% 7.94/1.51  --bmc1_deadlock                         false
% 7.94/1.51  --bmc1_ucm                              false
% 7.94/1.51  --bmc1_add_unsat_core                   none
% 7.94/1.51  --bmc1_unsat_core_children              false
% 7.94/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.94/1.51  --bmc1_out_stat                         full
% 7.94/1.51  --bmc1_ground_init                      false
% 7.94/1.51  --bmc1_pre_inst_next_state              false
% 7.94/1.51  --bmc1_pre_inst_state                   false
% 7.94/1.51  --bmc1_pre_inst_reach_state             false
% 7.94/1.51  --bmc1_out_unsat_core                   false
% 7.94/1.51  --bmc1_aig_witness_out                  false
% 7.94/1.51  --bmc1_verbose                          false
% 7.94/1.51  --bmc1_dump_clauses_tptp                false
% 7.94/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.94/1.51  --bmc1_dump_file                        -
% 7.94/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.94/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.94/1.51  --bmc1_ucm_extend_mode                  1
% 7.94/1.51  --bmc1_ucm_init_mode                    2
% 7.94/1.51  --bmc1_ucm_cone_mode                    none
% 7.94/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.94/1.51  --bmc1_ucm_relax_model                  4
% 7.94/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.94/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.94/1.51  --bmc1_ucm_layered_model                none
% 7.94/1.51  --bmc1_ucm_max_lemma_size               10
% 7.94/1.51  
% 7.94/1.51  ------ AIG Options
% 7.94/1.51  
% 7.94/1.51  --aig_mode                              false
% 7.94/1.51  
% 7.94/1.51  ------ Instantiation Options
% 7.94/1.51  
% 7.94/1.51  --instantiation_flag                    true
% 7.94/1.51  --inst_sos_flag                         false
% 7.94/1.51  --inst_sos_phase                        true
% 7.94/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.94/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.94/1.51  --inst_lit_sel_side                     num_symb
% 7.94/1.51  --inst_solver_per_active                1400
% 7.94/1.51  --inst_solver_calls_frac                1.
% 7.94/1.51  --inst_passive_queue_type               priority_queues
% 7.94/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.94/1.51  --inst_passive_queues_freq              [25;2]
% 7.94/1.51  --inst_dismatching                      true
% 7.94/1.51  --inst_eager_unprocessed_to_passive     true
% 7.94/1.51  --inst_prop_sim_given                   true
% 7.94/1.51  --inst_prop_sim_new                     false
% 7.94/1.51  --inst_subs_new                         false
% 7.94/1.51  --inst_eq_res_simp                      false
% 7.94/1.51  --inst_subs_given                       false
% 7.94/1.51  --inst_orphan_elimination               true
% 7.94/1.51  --inst_learning_loop_flag               true
% 7.94/1.51  --inst_learning_start                   3000
% 7.94/1.51  --inst_learning_factor                  2
% 7.94/1.51  --inst_start_prop_sim_after_learn       3
% 7.94/1.51  --inst_sel_renew                        solver
% 7.94/1.51  --inst_lit_activity_flag                true
% 7.94/1.51  --inst_restr_to_given                   false
% 7.94/1.51  --inst_activity_threshold               500
% 7.94/1.51  --inst_out_proof                        true
% 7.94/1.51  
% 7.94/1.51  ------ Resolution Options
% 7.94/1.51  
% 7.94/1.51  --resolution_flag                       true
% 7.94/1.51  --res_lit_sel                           adaptive
% 7.94/1.51  --res_lit_sel_side                      none
% 7.94/1.51  --res_ordering                          kbo
% 7.94/1.51  --res_to_prop_solver                    active
% 7.94/1.51  --res_prop_simpl_new                    false
% 7.94/1.51  --res_prop_simpl_given                  true
% 7.94/1.51  --res_passive_queue_type                priority_queues
% 7.94/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.94/1.51  --res_passive_queues_freq               [15;5]
% 7.94/1.51  --res_forward_subs                      full
% 7.94/1.51  --res_backward_subs                     full
% 7.94/1.51  --res_forward_subs_resolution           true
% 7.94/1.51  --res_backward_subs_resolution          true
% 7.94/1.51  --res_orphan_elimination                true
% 7.94/1.51  --res_time_limit                        2.
% 7.94/1.51  --res_out_proof                         true
% 7.94/1.51  
% 7.94/1.51  ------ Superposition Options
% 7.94/1.51  
% 7.94/1.51  --superposition_flag                    true
% 7.94/1.51  --sup_passive_queue_type                priority_queues
% 7.94/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.94/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.94/1.51  --demod_completeness_check              fast
% 7.94/1.51  --demod_use_ground                      true
% 7.94/1.51  --sup_to_prop_solver                    passive
% 7.94/1.51  --sup_prop_simpl_new                    true
% 7.94/1.51  --sup_prop_simpl_given                  true
% 7.94/1.51  --sup_fun_splitting                     false
% 7.94/1.51  --sup_smt_interval                      50000
% 7.94/1.51  
% 7.94/1.51  ------ Superposition Simplification Setup
% 7.94/1.51  
% 7.94/1.51  --sup_indices_passive                   []
% 7.94/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.94/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.51  --sup_full_bw                           [BwDemod]
% 7.94/1.51  --sup_immed_triv                        [TrivRules]
% 7.94/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.94/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.51  --sup_immed_bw_main                     []
% 7.94/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.94/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.94/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.94/1.51  
% 7.94/1.51  ------ Combination Options
% 7.94/1.51  
% 7.94/1.51  --comb_res_mult                         3
% 7.94/1.51  --comb_sup_mult                         2
% 7.94/1.51  --comb_inst_mult                        10
% 7.94/1.51  
% 7.94/1.51  ------ Debug Options
% 7.94/1.51  
% 7.94/1.51  --dbg_backtrace                         false
% 7.94/1.51  --dbg_dump_prop_clauses                 false
% 7.94/1.51  --dbg_dump_prop_clauses_file            -
% 7.94/1.51  --dbg_out_stat                          false
% 7.94/1.51  ------ Parsing...
% 7.94/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.94/1.51  
% 7.94/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.94/1.51  
% 7.94/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.94/1.51  
% 7.94/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.51  ------ Proving...
% 7.94/1.51  ------ Problem Properties 
% 7.94/1.51  
% 7.94/1.51  
% 7.94/1.51  clauses                                 59
% 7.94/1.51  conjectures                             23
% 7.94/1.52  EPR                                     18
% 7.94/1.52  Horn                                    38
% 7.94/1.52  unary                                   16
% 7.94/1.52  binary                                  19
% 7.94/1.52  lits                                    224
% 7.94/1.52  lits eq                                 6
% 7.94/1.52  fd_pure                                 0
% 7.94/1.52  fd_pseudo                               0
% 7.94/1.52  fd_cond                                 0
% 7.94/1.52  fd_pseudo_cond                          1
% 7.94/1.52  AC symbols                              0
% 7.94/1.52  
% 7.94/1.52  ------ Schedule dynamic 5 is on 
% 7.94/1.52  
% 7.94/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.94/1.52  
% 7.94/1.52  
% 7.94/1.52  ------ 
% 7.94/1.52  Current options:
% 7.94/1.52  ------ 
% 7.94/1.52  
% 7.94/1.52  ------ Input Options
% 7.94/1.52  
% 7.94/1.52  --out_options                           all
% 7.94/1.52  --tptp_safe_out                         true
% 7.94/1.52  --problem_path                          ""
% 7.94/1.52  --include_path                          ""
% 7.94/1.52  --clausifier                            res/vclausify_rel
% 7.94/1.52  --clausifier_options                    --mode clausify
% 7.94/1.52  --stdin                                 false
% 7.94/1.52  --stats_out                             all
% 7.94/1.52  
% 7.94/1.52  ------ General Options
% 7.94/1.52  
% 7.94/1.52  --fof                                   false
% 7.94/1.52  --time_out_real                         305.
% 7.94/1.52  --time_out_virtual                      -1.
% 7.94/1.52  --symbol_type_check                     false
% 7.94/1.52  --clausify_out                          false
% 7.94/1.52  --sig_cnt_out                           false
% 7.94/1.52  --trig_cnt_out                          false
% 7.94/1.52  --trig_cnt_out_tolerance                1.
% 7.94/1.52  --trig_cnt_out_sk_spl                   false
% 7.94/1.52  --abstr_cl_out                          false
% 7.94/1.52  
% 7.94/1.52  ------ Global Options
% 7.94/1.52  
% 7.94/1.52  --schedule                              default
% 7.94/1.52  --add_important_lit                     false
% 7.94/1.52  --prop_solver_per_cl                    1000
% 7.94/1.52  --min_unsat_core                        false
% 7.94/1.52  --soft_assumptions                      false
% 7.94/1.52  --soft_lemma_size                       3
% 7.94/1.52  --prop_impl_unit_size                   0
% 7.94/1.52  --prop_impl_unit                        []
% 7.94/1.52  --share_sel_clauses                     true
% 7.94/1.52  --reset_solvers                         false
% 7.94/1.52  --bc_imp_inh                            [conj_cone]
% 7.94/1.52  --conj_cone_tolerance                   3.
% 7.94/1.52  --extra_neg_conj                        none
% 7.94/1.52  --large_theory_mode                     true
% 7.94/1.52  --prolific_symb_bound                   200
% 7.94/1.52  --lt_threshold                          2000
% 7.94/1.52  --clause_weak_htbl                      true
% 7.94/1.52  --gc_record_bc_elim                     false
% 7.94/1.52  
% 7.94/1.52  ------ Preprocessing Options
% 7.94/1.52  
% 7.94/1.52  --preprocessing_flag                    true
% 7.94/1.52  --time_out_prep_mult                    0.1
% 7.94/1.52  --splitting_mode                        input
% 7.94/1.52  --splitting_grd                         true
% 7.94/1.52  --splitting_cvd                         false
% 7.94/1.52  --splitting_cvd_svl                     false
% 7.94/1.52  --splitting_nvd                         32
% 7.94/1.52  --sub_typing                            true
% 7.94/1.52  --prep_gs_sim                           true
% 7.94/1.52  --prep_unflatten                        true
% 7.94/1.52  --prep_res_sim                          true
% 7.94/1.52  --prep_upred                            true
% 7.94/1.52  --prep_sem_filter                       exhaustive
% 7.94/1.52  --prep_sem_filter_out                   false
% 7.94/1.52  --pred_elim                             true
% 7.94/1.52  --res_sim_input                         true
% 7.94/1.52  --eq_ax_congr_red                       true
% 7.94/1.52  --pure_diseq_elim                       true
% 7.94/1.52  --brand_transform                       false
% 7.94/1.52  --non_eq_to_eq                          false
% 7.94/1.52  --prep_def_merge                        true
% 7.94/1.52  --prep_def_merge_prop_impl              false
% 7.94/1.52  --prep_def_merge_mbd                    true
% 7.94/1.52  --prep_def_merge_tr_red                 false
% 7.94/1.52  --prep_def_merge_tr_cl                  false
% 7.94/1.52  --smt_preprocessing                     true
% 7.94/1.52  --smt_ac_axioms                         fast
% 7.94/1.52  --preprocessed_out                      false
% 7.94/1.52  --preprocessed_stats                    false
% 7.94/1.52  
% 7.94/1.52  ------ Abstraction refinement Options
% 7.94/1.52  
% 7.94/1.52  --abstr_ref                             []
% 7.94/1.52  --abstr_ref_prep                        false
% 7.94/1.52  --abstr_ref_until_sat                   false
% 7.94/1.52  --abstr_ref_sig_restrict                funpre
% 7.94/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.94/1.52  --abstr_ref_under                       []
% 7.94/1.52  
% 7.94/1.52  ------ SAT Options
% 7.94/1.52  
% 7.94/1.52  --sat_mode                              false
% 7.94/1.52  --sat_fm_restart_options                ""
% 7.94/1.52  --sat_gr_def                            false
% 7.94/1.52  --sat_epr_types                         true
% 7.94/1.52  --sat_non_cyclic_types                  false
% 7.94/1.52  --sat_finite_models                     false
% 7.94/1.52  --sat_fm_lemmas                         false
% 7.94/1.52  --sat_fm_prep                           false
% 7.94/1.52  --sat_fm_uc_incr                        true
% 7.94/1.52  --sat_out_model                         small
% 7.94/1.52  --sat_out_clauses                       false
% 7.94/1.52  
% 7.94/1.52  ------ QBF Options
% 7.94/1.52  
% 7.94/1.52  --qbf_mode                              false
% 7.94/1.52  --qbf_elim_univ                         false
% 7.94/1.52  --qbf_dom_inst                          none
% 7.94/1.52  --qbf_dom_pre_inst                      false
% 7.94/1.52  --qbf_sk_in                             false
% 7.94/1.52  --qbf_pred_elim                         true
% 7.94/1.52  --qbf_split                             512
% 7.94/1.52  
% 7.94/1.52  ------ BMC1 Options
% 7.94/1.52  
% 7.94/1.52  --bmc1_incremental                      false
% 7.94/1.52  --bmc1_axioms                           reachable_all
% 7.94/1.52  --bmc1_min_bound                        0
% 7.94/1.52  --bmc1_max_bound                        -1
% 7.94/1.52  --bmc1_max_bound_default                -1
% 7.94/1.52  --bmc1_symbol_reachability              true
% 7.94/1.52  --bmc1_property_lemmas                  false
% 7.94/1.52  --bmc1_k_induction                      false
% 7.94/1.52  --bmc1_non_equiv_states                 false
% 7.94/1.52  --bmc1_deadlock                         false
% 7.94/1.52  --bmc1_ucm                              false
% 7.94/1.52  --bmc1_add_unsat_core                   none
% 7.94/1.52  --bmc1_unsat_core_children              false
% 7.94/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.94/1.52  --bmc1_out_stat                         full
% 7.94/1.52  --bmc1_ground_init                      false
% 7.94/1.52  --bmc1_pre_inst_next_state              false
% 7.94/1.52  --bmc1_pre_inst_state                   false
% 7.94/1.52  --bmc1_pre_inst_reach_state             false
% 7.94/1.52  --bmc1_out_unsat_core                   false
% 7.94/1.52  --bmc1_aig_witness_out                  false
% 7.94/1.52  --bmc1_verbose                          false
% 7.94/1.52  --bmc1_dump_clauses_tptp                false
% 7.94/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.94/1.52  --bmc1_dump_file                        -
% 7.94/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.94/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.94/1.52  --bmc1_ucm_extend_mode                  1
% 7.94/1.52  --bmc1_ucm_init_mode                    2
% 7.94/1.52  --bmc1_ucm_cone_mode                    none
% 7.94/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.94/1.52  --bmc1_ucm_relax_model                  4
% 7.94/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.94/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.94/1.52  --bmc1_ucm_layered_model                none
% 7.94/1.52  --bmc1_ucm_max_lemma_size               10
% 7.94/1.52  
% 7.94/1.52  ------ AIG Options
% 7.94/1.52  
% 7.94/1.52  --aig_mode                              false
% 7.94/1.52  
% 7.94/1.52  ------ Instantiation Options
% 7.94/1.52  
% 7.94/1.52  --instantiation_flag                    true
% 7.94/1.52  --inst_sos_flag                         false
% 7.94/1.52  --inst_sos_phase                        true
% 7.94/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.94/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.94/1.52  --inst_lit_sel_side                     none
% 7.94/1.52  --inst_solver_per_active                1400
% 7.94/1.52  --inst_solver_calls_frac                1.
% 7.94/1.52  --inst_passive_queue_type               priority_queues
% 7.94/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.94/1.52  --inst_passive_queues_freq              [25;2]
% 7.94/1.52  --inst_dismatching                      true
% 7.94/1.52  --inst_eager_unprocessed_to_passive     true
% 7.94/1.52  --inst_prop_sim_given                   true
% 7.94/1.52  --inst_prop_sim_new                     false
% 7.94/1.52  --inst_subs_new                         false
% 7.94/1.52  --inst_eq_res_simp                      false
% 7.94/1.52  --inst_subs_given                       false
% 7.94/1.52  --inst_orphan_elimination               true
% 7.94/1.52  --inst_learning_loop_flag               true
% 7.94/1.52  --inst_learning_start                   3000
% 7.94/1.52  --inst_learning_factor                  2
% 7.94/1.52  --inst_start_prop_sim_after_learn       3
% 7.94/1.52  --inst_sel_renew                        solver
% 7.94/1.52  --inst_lit_activity_flag                true
% 7.94/1.52  --inst_restr_to_given                   false
% 7.94/1.52  --inst_activity_threshold               500
% 7.94/1.52  --inst_out_proof                        true
% 7.94/1.52  
% 7.94/1.52  ------ Resolution Options
% 7.94/1.52  
% 7.94/1.52  --resolution_flag                       false
% 7.94/1.52  --res_lit_sel                           adaptive
% 7.94/1.52  --res_lit_sel_side                      none
% 7.94/1.52  --res_ordering                          kbo
% 7.94/1.52  --res_to_prop_solver                    active
% 7.94/1.52  --res_prop_simpl_new                    false
% 7.94/1.52  --res_prop_simpl_given                  true
% 7.94/1.52  --res_passive_queue_type                priority_queues
% 7.94/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.94/1.52  --res_passive_queues_freq               [15;5]
% 7.94/1.52  --res_forward_subs                      full
% 7.94/1.52  --res_backward_subs                     full
% 7.94/1.52  --res_forward_subs_resolution           true
% 7.94/1.52  --res_backward_subs_resolution          true
% 7.94/1.52  --res_orphan_elimination                true
% 7.94/1.52  --res_time_limit                        2.
% 7.94/1.52  --res_out_proof                         true
% 7.94/1.52  
% 7.94/1.52  ------ Superposition Options
% 7.94/1.52  
% 7.94/1.52  --superposition_flag                    true
% 7.94/1.52  --sup_passive_queue_type                priority_queues
% 7.94/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.94/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.94/1.52  --demod_completeness_check              fast
% 7.94/1.52  --demod_use_ground                      true
% 7.94/1.52  --sup_to_prop_solver                    passive
% 7.94/1.52  --sup_prop_simpl_new                    true
% 7.94/1.52  --sup_prop_simpl_given                  true
% 7.94/1.52  --sup_fun_splitting                     false
% 7.94/1.52  --sup_smt_interval                      50000
% 7.94/1.52  
% 7.94/1.52  ------ Superposition Simplification Setup
% 7.94/1.52  
% 7.94/1.52  --sup_indices_passive                   []
% 7.94/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.94/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.52  --sup_full_bw                           [BwDemod]
% 7.94/1.52  --sup_immed_triv                        [TrivRules]
% 7.94/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.94/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.52  --sup_immed_bw_main                     []
% 7.94/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.94/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.94/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.94/1.52  
% 7.94/1.52  ------ Combination Options
% 7.94/1.52  
% 7.94/1.52  --comb_res_mult                         3
% 7.94/1.52  --comb_sup_mult                         2
% 7.94/1.52  --comb_inst_mult                        10
% 7.94/1.52  
% 7.94/1.52  ------ Debug Options
% 7.94/1.52  
% 7.94/1.52  --dbg_backtrace                         false
% 7.94/1.52  --dbg_dump_prop_clauses                 false
% 7.94/1.52  --dbg_dump_prop_clauses_file            -
% 7.94/1.52  --dbg_out_stat                          false
% 7.94/1.52  
% 7.94/1.52  
% 7.94/1.52  
% 7.94/1.52  
% 7.94/1.52  ------ Proving...
% 7.94/1.52  
% 7.94/1.52  
% 7.94/1.52  % SZS status Theorem for theBenchmark.p
% 7.94/1.52  
% 7.94/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.94/1.52  
% 7.94/1.52  fof(f18,axiom,(
% 7.94/1.52    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.94/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.52  
% 7.94/1.52  fof(f47,plain,(
% 7.94/1.52    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.94/1.52    inference(ennf_transformation,[],[f18])).
% 7.94/1.52  
% 7.94/1.52  fof(f109,plain,(
% 7.94/1.52    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.94/1.52    inference(cnf_transformation,[],[f47])).
% 7.94/1.52  
% 7.94/1.52  fof(f20,conjecture,(
% 7.94/1.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 7.94/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.52  
% 7.94/1.52  fof(f21,negated_conjecture,(
% 7.94/1.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 7.94/1.52    inference(negated_conjecture,[],[f20])).
% 7.94/1.52  
% 7.94/1.52  fof(f50,plain,(
% 7.94/1.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & (r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0)) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.94/1.52    inference(ennf_transformation,[],[f21])).
% 7.94/1.52  
% 7.94/1.52  fof(f51,plain,(
% 7.94/1.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.94/1.52    inference(flattening,[],[f50])).
% 7.94/1.52  
% 7.94/1.52  fof(f64,plain,(
% 7.94/1.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.94/1.52    inference(nnf_transformation,[],[f51])).
% 7.94/1.52  
% 7.94/1.52  fof(f65,plain,(
% 7.94/1.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.94/1.52    inference(flattening,[],[f64])).
% 7.94/1.52  
% 7.94/1.52  fof(f70,plain,(
% 7.94/1.52    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((~m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,sK6) & k1_tsep_1(X0,X3,sK6) = X0 & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 7.94/1.52    introduced(choice_axiom,[])).
% 7.94/1.52  
% 7.94/1.52  fof(f69,plain,(
% 7.94/1.52    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK5)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK5))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,sK5,X4) & k1_tsep_1(X0,sK5,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 7.94/1.52    introduced(choice_axiom,[])).
% 7.94/1.52  
% 7.94/1.52  fof(f68,plain,(
% 7.94/1.52    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(sK4,X0,X1) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) & m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X3))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK4,X0,X1) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 7.94/1.52    introduced(choice_axiom,[])).
% 7.94/1.52  
% 7.94/1.52  fof(f67,plain,(
% 7.94/1.52    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(X2,X0,sK3) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) & m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v5_pre_topc(X2,X0,sK3) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 7.94/1.52    introduced(choice_axiom,[])).
% 7.94/1.52  
% 7.94/1.52  fof(f66,plain,(
% 7.94/1.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(sK2,X3,X4) & k1_tsep_1(sK2,X3,X4) = sK2 & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 7.94/1.52    introduced(choice_axiom,[])).
% 7.94/1.52  
% 7.94/1.52  fof(f71,plain,(
% 7.94/1.52    (((((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,sK5,sK6) & k1_tsep_1(sK2,sK5,sK6) = sK2 & m1_pre_topc(sK6,sK2) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 7.94/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f65,f70,f69,f68,f67,f66])).
% 7.94/1.52  
% 7.94/1.52  fof(f119,plain,(
% 7.94/1.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f11,axiom,(
% 7.94/1.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 7.94/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.52  
% 7.94/1.52  fof(f34,plain,(
% 7.94/1.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.94/1.52    inference(ennf_transformation,[],[f11])).
% 7.94/1.52  
% 7.94/1.52  fof(f35,plain,(
% 7.94/1.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.94/1.52    inference(flattening,[],[f34])).
% 7.94/1.52  
% 7.94/1.52  fof(f85,plain,(
% 7.94/1.52    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.94/1.52    inference(cnf_transformation,[],[f35])).
% 7.94/1.52  
% 7.94/1.52  fof(f7,axiom,(
% 7.94/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.94/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.52  
% 7.94/1.52  fof(f28,plain,(
% 7.94/1.52    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.94/1.52    inference(ennf_transformation,[],[f7])).
% 7.94/1.52  
% 7.94/1.52  fof(f29,plain,(
% 7.94/1.52    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.94/1.52    inference(flattening,[],[f28])).
% 7.94/1.52  
% 7.94/1.52  fof(f81,plain,(
% 7.94/1.52    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.94/1.52    inference(cnf_transformation,[],[f29])).
% 7.94/1.52  
% 7.94/1.52  fof(f117,plain,(
% 7.94/1.52    v1_funct_1(sK4)),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f111,plain,(
% 7.94/1.52    ~v2_struct_0(sK2)),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f112,plain,(
% 7.94/1.52    v2_pre_topc(sK2)),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f113,plain,(
% 7.94/1.52    l1_pre_topc(sK2)),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f114,plain,(
% 7.94/1.52    ~v2_struct_0(sK3)),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f115,plain,(
% 7.94/1.52    v2_pre_topc(sK3)),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f116,plain,(
% 7.94/1.52    l1_pre_topc(sK3)),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f118,plain,(
% 7.94/1.52    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f6,axiom,(
% 7.94/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.94/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.52  
% 7.94/1.52  fof(f23,plain,(
% 7.94/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.94/1.52    inference(pure_predicate_removal,[],[f6])).
% 7.94/1.52  
% 7.94/1.52  fof(f27,plain,(
% 7.94/1.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.94/1.52    inference(ennf_transformation,[],[f23])).
% 7.94/1.52  
% 7.94/1.52  fof(f80,plain,(
% 7.94/1.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.94/1.52    inference(cnf_transformation,[],[f27])).
% 7.94/1.52  
% 7.94/1.52  fof(f5,axiom,(
% 7.94/1.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.94/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.52  
% 7.94/1.52  fof(f25,plain,(
% 7.94/1.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.94/1.52    inference(ennf_transformation,[],[f5])).
% 7.94/1.52  
% 7.94/1.52  fof(f26,plain,(
% 7.94/1.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.94/1.52    inference(flattening,[],[f25])).
% 7.94/1.52  
% 7.94/1.52  fof(f79,plain,(
% 7.94/1.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.94/1.52    inference(cnf_transformation,[],[f26])).
% 7.94/1.52  
% 7.94/1.52  fof(f2,axiom,(
% 7.94/1.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.94/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.52  
% 7.94/1.52  fof(f57,plain,(
% 7.94/1.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.94/1.52    inference(nnf_transformation,[],[f2])).
% 7.94/1.52  
% 7.94/1.52  fof(f75,plain,(
% 7.94/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.94/1.52    inference(cnf_transformation,[],[f57])).
% 7.94/1.52  
% 7.94/1.52  fof(f3,axiom,(
% 7.94/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.94/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.52  
% 7.94/1.52  fof(f24,plain,(
% 7.94/1.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.94/1.52    inference(ennf_transformation,[],[f3])).
% 7.94/1.52  
% 7.94/1.52  fof(f77,plain,(
% 7.94/1.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.94/1.52    inference(cnf_transformation,[],[f24])).
% 7.94/1.52  
% 7.94/1.52  fof(f76,plain,(
% 7.94/1.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.94/1.52    inference(cnf_transformation,[],[f57])).
% 7.94/1.52  
% 7.94/1.52  fof(f4,axiom,(
% 7.94/1.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.94/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.52  
% 7.94/1.52  fof(f78,plain,(
% 7.94/1.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.94/1.52    inference(cnf_transformation,[],[f4])).
% 7.94/1.52  
% 7.94/1.52  fof(f53,plain,(
% 7.94/1.52    ! [X2,X0,X4,X3,X1] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> sP0(X1,X3,X4,X0,X2)) | ~sP1(X2,X0,X4,X3,X1))),
% 7.94/1.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 7.94/1.52  
% 7.94/1.52  fof(f58,plain,(
% 7.94/1.52    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))))) | ~sP1(X2,X0,X4,X3,X1))),
% 7.94/1.52    inference(nnf_transformation,[],[f53])).
% 7.94/1.52  
% 7.94/1.52  fof(f59,plain,(
% 7.94/1.52    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))))) | ~sP1(X2,X0,X4,X3,X1))),
% 7.94/1.52    inference(flattening,[],[f58])).
% 7.94/1.52  
% 7.94/1.52  fof(f60,plain,(
% 7.94/1.52    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) & v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) & v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) & v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))))) | ~sP1(X0,X1,X2,X3,X4))),
% 7.94/1.52    inference(rectify,[],[f59])).
% 7.94/1.52  
% 7.94/1.52  fof(f91,plain,(
% 7.94/1.52    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.94/1.52    inference(cnf_transformation,[],[f60])).
% 7.94/1.52  
% 7.94/1.52  fof(f14,axiom,(
% 7.94/1.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))))))))),
% 7.94/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.52  
% 7.94/1.52  fof(f40,plain,(
% 7.94/1.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.94/1.52    inference(ennf_transformation,[],[f14])).
% 7.94/1.52  
% 7.94/1.52  fof(f41,plain,(
% 7.94/1.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.94/1.52    inference(flattening,[],[f40])).
% 7.94/1.52  
% 7.94/1.52  fof(f52,plain,(
% 7.94/1.52    ! [X1,X3,X4,X0,X2] : (sP0(X1,X3,X4,X0,X2) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))),
% 7.94/1.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.94/1.52  
% 7.94/1.52  fof(f54,plain,(
% 7.94/1.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X2,X0,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.94/1.52    inference(definition_folding,[],[f41,f53,f52])).
% 7.94/1.52  
% 7.94/1.52  fof(f105,plain,(
% 7.94/1.52    ( ! [X4,X2,X0,X3,X1] : (sP1(X2,X0,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.94/1.52    inference(cnf_transformation,[],[f54])).
% 7.94/1.52  
% 7.94/1.52  fof(f125,plain,(
% 7.94/1.52    r4_tsep_1(sK2,sK5,sK6)),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f120,plain,(
% 7.94/1.52    ~v2_struct_0(sK5)),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f121,plain,(
% 7.94/1.52    m1_pre_topc(sK5,sK2)),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f122,plain,(
% 7.94/1.52    ~v2_struct_0(sK6)),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f123,plain,(
% 7.94/1.52    m1_pre_topc(sK6,sK2)),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f124,plain,(
% 7.94/1.52    k1_tsep_1(sK2,sK5,sK6) = sK2),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f93,plain,(
% 7.94/1.52    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.94/1.52    inference(cnf_transformation,[],[f60])).
% 7.94/1.52  
% 7.94/1.52  fof(f95,plain,(
% 7.94/1.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.94/1.52    inference(cnf_transformation,[],[f60])).
% 7.94/1.52  
% 7.94/1.52  fof(f156,plain,(
% 7.94/1.52    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f61,plain,(
% 7.94/1.52    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 7.94/1.52    inference(nnf_transformation,[],[f52])).
% 7.94/1.52  
% 7.94/1.52  fof(f62,plain,(
% 7.94/1.52    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 7.94/1.52    inference(flattening,[],[f61])).
% 7.94/1.52  
% 7.94/1.52  fof(f63,plain,(
% 7.94/1.52    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) & ((m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 7.94/1.52    inference(rectify,[],[f62])).
% 7.94/1.52  
% 7.94/1.52  fof(f104,plain,(
% 7.94/1.52    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) )),
% 7.94/1.52    inference(cnf_transformation,[],[f63])).
% 7.94/1.52  
% 7.94/1.52  fof(f144,plain,(
% 7.94/1.52    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | v5_pre_topc(sK4,sK2,sK3)),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f148,plain,(
% 7.94/1.52    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f152,plain,(
% 7.94/1.52    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f94,plain,(
% 7.94/1.52    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.94/1.52    inference(cnf_transformation,[],[f60])).
% 7.94/1.52  
% 7.94/1.52  fof(f140,plain,(
% 7.94/1.52    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f128,plain,(
% 7.94/1.52    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | v5_pre_topc(sK4,sK2,sK3)),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f132,plain,(
% 7.94/1.52    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f136,plain,(
% 7.94/1.52    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  fof(f92,plain,(
% 7.94/1.52    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.94/1.52    inference(cnf_transformation,[],[f60])).
% 7.94/1.52  
% 7.94/1.52  fof(f102,plain,(
% 7.94/1.52    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 7.94/1.52    inference(cnf_transformation,[],[f63])).
% 7.94/1.52  
% 7.94/1.52  fof(f13,axiom,(
% 7.94/1.52    ! [X0,X1,X2,X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 7.94/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.52  
% 7.94/1.52  fof(f38,plain,(
% 7.94/1.52    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.94/1.52    inference(ennf_transformation,[],[f13])).
% 7.94/1.52  
% 7.94/1.52  fof(f39,plain,(
% 7.94/1.52    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.94/1.52    inference(flattening,[],[f38])).
% 7.94/1.52  
% 7.94/1.52  fof(f90,plain,(
% 7.94/1.52    ( ! [X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.94/1.52    inference(cnf_transformation,[],[f39])).
% 7.94/1.52  
% 7.94/1.52  fof(f103,plain,(
% 7.94/1.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP0(X0,X1,X2,X3,X4)) )),
% 7.94/1.52    inference(cnf_transformation,[],[f63])).
% 7.94/1.52  
% 7.94/1.52  fof(f99,plain,(
% 7.94/1.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~sP0(X0,X1,X2,X3,X4)) )),
% 7.94/1.52    inference(cnf_transformation,[],[f63])).
% 7.94/1.52  
% 7.94/1.52  fof(f88,plain,(
% 7.94/1.52    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.94/1.52    inference(cnf_transformation,[],[f39])).
% 7.94/1.52  
% 7.94/1.52  fof(f89,plain,(
% 7.94/1.52    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.94/1.52    inference(cnf_transformation,[],[f39])).
% 7.94/1.52  
% 7.94/1.52  fof(f158,plain,(
% 7.94/1.52    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 7.94/1.52    inference(cnf_transformation,[],[f71])).
% 7.94/1.52  
% 7.94/1.52  cnf(c_37,plain,
% 7.94/1.52      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.94/1.52      inference(cnf_transformation,[],[f109]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4140,plain,
% 7.94/1.52      ( m1_pre_topc(X0,X0) = iProver_top
% 7.94/1.52      | l1_pre_topc(X0) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_78,negated_conjecture,
% 7.94/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 7.94/1.52      inference(cnf_transformation,[],[f119]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4126,plain,
% 7.94/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_78]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_13,plain,
% 7.94/1.52      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.94/1.52      | ~ m1_pre_topc(X3,X1)
% 7.94/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.94/1.52      | v2_struct_0(X1)
% 7.94/1.52      | v2_struct_0(X2)
% 7.94/1.52      | ~ l1_pre_topc(X1)
% 7.94/1.52      | ~ l1_pre_topc(X2)
% 7.94/1.52      | ~ v2_pre_topc(X1)
% 7.94/1.52      | ~ v2_pre_topc(X2)
% 7.94/1.52      | ~ v1_funct_1(X0)
% 7.94/1.52      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 7.94/1.52      inference(cnf_transformation,[],[f85]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4158,plain,
% 7.94/1.52      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
% 7.94/1.52      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 7.94/1.52      | m1_pre_topc(X3,X0) != iProver_top
% 7.94/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 7.94/1.52      | v2_struct_0(X0) = iProver_top
% 7.94/1.52      | v2_struct_0(X1) = iProver_top
% 7.94/1.52      | l1_pre_topc(X0) != iProver_top
% 7.94/1.52      | l1_pre_topc(X1) != iProver_top
% 7.94/1.52      | v2_pre_topc(X0) != iProver_top
% 7.94/1.52      | v2_pre_topc(X1) != iProver_top
% 7.94/1.52      | v1_funct_1(X2) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_9534,plain,
% 7.94/1.52      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0)) = k2_tmap_1(sK2,sK3,sK4,X0)
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_pre_topc(X0,sK2) != iProver_top
% 7.94/1.52      | v2_struct_0(sK3) = iProver_top
% 7.94/1.52      | v2_struct_0(sK2) = iProver_top
% 7.94/1.52      | l1_pre_topc(sK3) != iProver_top
% 7.94/1.52      | l1_pre_topc(sK2) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK3) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_4126,c_4158]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_9,plain,
% 7.94/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.94/1.52      | ~ v1_funct_1(X0)
% 7.94/1.52      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.94/1.52      inference(cnf_transformation,[],[f81]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4162,plain,
% 7.94/1.52      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 7.94/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.94/1.52      | v1_funct_1(X2) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_8556,plain,
% 7.94/1.52      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k7_relat_1(sK4,X0)
% 7.94/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_4126,c_4162]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_80,negated_conjecture,
% 7.94/1.52      ( v1_funct_1(sK4) ),
% 7.94/1.52      inference(cnf_transformation,[],[f117]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4833,plain,
% 7.94/1.52      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.94/1.52      | ~ v1_funct_1(sK4)
% 7.94/1.52      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_9]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4934,plain,
% 7.94/1.52      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.94/1.52      | ~ v1_funct_1(sK4)
% 7.94/1.52      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k7_relat_1(sK4,X0) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_4833]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_9049,plain,
% 7.94/1.52      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k7_relat_1(sK4,X0) ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_8556,c_80,c_78,c_4934]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_9574,plain,
% 7.94/1.52      ( k2_tmap_1(sK2,sK3,sK4,X0) = k7_relat_1(sK4,u1_struct_0(X0))
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_pre_topc(X0,sK2) != iProver_top
% 7.94/1.52      | v2_struct_0(sK3) = iProver_top
% 7.94/1.52      | v2_struct_0(sK2) = iProver_top
% 7.94/1.52      | l1_pre_topc(sK3) != iProver_top
% 7.94/1.52      | l1_pre_topc(sK2) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK3) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.52      inference(demodulation,[status(thm)],[c_9534,c_9049]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_86,negated_conjecture,
% 7.94/1.52      ( ~ v2_struct_0(sK2) ),
% 7.94/1.52      inference(cnf_transformation,[],[f111]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_87,plain,
% 7.94/1.52      ( v2_struct_0(sK2) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_86]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_85,negated_conjecture,
% 7.94/1.52      ( v2_pre_topc(sK2) ),
% 7.94/1.52      inference(cnf_transformation,[],[f112]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_88,plain,
% 7.94/1.52      ( v2_pre_topc(sK2) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_85]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_84,negated_conjecture,
% 7.94/1.52      ( l1_pre_topc(sK2) ),
% 7.94/1.52      inference(cnf_transformation,[],[f113]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_89,plain,
% 7.94/1.52      ( l1_pre_topc(sK2) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_84]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_83,negated_conjecture,
% 7.94/1.52      ( ~ v2_struct_0(sK3) ),
% 7.94/1.52      inference(cnf_transformation,[],[f114]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_90,plain,
% 7.94/1.52      ( v2_struct_0(sK3) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_83]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_82,negated_conjecture,
% 7.94/1.52      ( v2_pre_topc(sK3) ),
% 7.94/1.52      inference(cnf_transformation,[],[f115]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_91,plain,
% 7.94/1.52      ( v2_pre_topc(sK3) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_82]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_81,negated_conjecture,
% 7.94/1.52      ( l1_pre_topc(sK3) ),
% 7.94/1.52      inference(cnf_transformation,[],[f116]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_92,plain,
% 7.94/1.52      ( l1_pre_topc(sK3) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_81]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_93,plain,
% 7.94/1.52      ( v1_funct_1(sK4) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_80]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_79,negated_conjecture,
% 7.94/1.52      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 7.94/1.52      inference(cnf_transformation,[],[f118]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_94,plain,
% 7.94/1.52      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_79]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_19622,plain,
% 7.94/1.52      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.94/1.52      | k2_tmap_1(sK2,sK3,sK4,X0) = k7_relat_1(sK4,u1_struct_0(X0)) ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_9574,c_87,c_88,c_89,c_90,c_91,c_92,c_93,c_94]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_19623,plain,
% 7.94/1.52      ( k2_tmap_1(sK2,sK3,sK4,X0) = k7_relat_1(sK4,u1_struct_0(X0))
% 7.94/1.52      | m1_pre_topc(X0,sK2) != iProver_top ),
% 7.94/1.52      inference(renaming,[status(thm)],[c_19622]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_19631,plain,
% 7.94/1.52      ( k2_tmap_1(sK2,sK3,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2))
% 7.94/1.52      | l1_pre_topc(sK2) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_4140,c_19623]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_8,plain,
% 7.94/1.52      ( v4_relat_1(X0,X1)
% 7.94/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.94/1.52      inference(cnf_transformation,[],[f80]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_7,plain,
% 7.94/1.52      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.94/1.52      inference(cnf_transformation,[],[f79]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_998,plain,
% 7.94/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.94/1.52      | ~ v1_relat_1(X0)
% 7.94/1.52      | k7_relat_1(X0,X1) = X0 ),
% 7.94/1.52      inference(resolution,[status(thm)],[c_8,c_7]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4115,plain,
% 7.94/1.52      ( k7_relat_1(X0,X1) = X0
% 7.94/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.94/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_998]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4891,plain,
% 7.94/1.52      ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK4
% 7.94/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_4126,c_4115]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4892,plain,
% 7.94/1.52      ( ~ v1_relat_1(sK4) | k7_relat_1(sK4,u1_struct_0(sK2)) = sK4 ),
% 7.94/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_4891]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4,plain,
% 7.94/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.94/1.52      inference(cnf_transformation,[],[f75]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4977,plain,
% 7.94/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.94/1.52      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_4]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5159,plain,
% 7.94/1.52      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.94/1.52      | r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_4977]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5,plain,
% 7.94/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.94/1.52      | ~ v1_relat_1(X1)
% 7.94/1.52      | v1_relat_1(X0) ),
% 7.94/1.52      inference(cnf_transformation,[],[f77]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_3,plain,
% 7.94/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.94/1.52      inference(cnf_transformation,[],[f76]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_672,plain,
% 7.94/1.52      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.94/1.52      inference(prop_impl,[status(thm)],[c_3]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_673,plain,
% 7.94/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.94/1.52      inference(renaming,[status(thm)],[c_672]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_794,plain,
% 7.94/1.52      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.94/1.52      inference(bin_hyper_res,[status(thm)],[c_5,c_673]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4876,plain,
% 7.94/1.52      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 7.94/1.52      | v1_relat_1(X0)
% 7.94/1.52      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_794]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5245,plain,
% 7.94/1.52      ( ~ r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
% 7.94/1.52      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
% 7.94/1.52      | v1_relat_1(sK4) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_4876]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_6,plain,
% 7.94/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.94/1.52      inference(cnf_transformation,[],[f78]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5855,plain,
% 7.94/1.52      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_6]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_6320,plain,
% 7.94/1.52      ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK4 ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_4891,c_78,c_4892,c_5159,c_5245,c_5855]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_19668,plain,
% 7.94/1.52      ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4
% 7.94/1.52      | l1_pre_topc(sK2) != iProver_top ),
% 7.94/1.52      inference(light_normalisation,[status(thm)],[c_19631,c_6320]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_20897,plain,
% 7.94/1.52      ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4 ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_19668,c_89]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_23,plain,
% 7.94/1.52      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.94/1.52      | sP0(X4,X3,X2,X1,X0)
% 7.94/1.52      | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
% 7.94/1.52      | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
% 7.94/1.52      | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
% 7.94/1.52      | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
% 7.94/1.52      inference(cnf_transformation,[],[f91]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_33,plain,
% 7.94/1.52      ( sP1(X0,X1,X2,X3,X4)
% 7.94/1.52      | ~ r4_tsep_1(X1,X0,X3)
% 7.94/1.52      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
% 7.94/1.52      | ~ m1_pre_topc(X3,X1)
% 7.94/1.52      | ~ m1_pre_topc(X0,X1)
% 7.94/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 7.94/1.52      | v2_struct_0(X1)
% 7.94/1.52      | v2_struct_0(X4)
% 7.94/1.52      | v2_struct_0(X0)
% 7.94/1.52      | v2_struct_0(X3)
% 7.94/1.52      | ~ l1_pre_topc(X1)
% 7.94/1.52      | ~ l1_pre_topc(X4)
% 7.94/1.52      | ~ v2_pre_topc(X1)
% 7.94/1.52      | ~ v2_pre_topc(X4)
% 7.94/1.52      | ~ v1_funct_1(X2) ),
% 7.94/1.52      inference(cnf_transformation,[],[f105]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_72,negated_conjecture,
% 7.94/1.52      ( r4_tsep_1(sK2,sK5,sK6) ),
% 7.94/1.52      inference(cnf_transformation,[],[f125]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_1016,plain,
% 7.94/1.52      ( sP1(X0,X1,X2,X3,X4)
% 7.94/1.52      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
% 7.94/1.52      | ~ m1_pre_topc(X0,X1)
% 7.94/1.52      | ~ m1_pre_topc(X3,X1)
% 7.94/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 7.94/1.52      | v2_struct_0(X0)
% 7.94/1.52      | v2_struct_0(X1)
% 7.94/1.52      | v2_struct_0(X3)
% 7.94/1.52      | v2_struct_0(X4)
% 7.94/1.52      | ~ l1_pre_topc(X1)
% 7.94/1.52      | ~ l1_pre_topc(X4)
% 7.94/1.52      | ~ v2_pre_topc(X1)
% 7.94/1.52      | ~ v2_pre_topc(X4)
% 7.94/1.52      | ~ v1_funct_1(X2)
% 7.94/1.52      | sK5 != X0
% 7.94/1.52      | sK6 != X3
% 7.94/1.52      | sK2 != X1 ),
% 7.94/1.52      inference(resolution_lifted,[status(thm)],[c_33,c_72]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_1017,plain,
% 7.94/1.52      ( sP1(sK5,sK2,X0,sK6,X1)
% 7.94/1.52      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 7.94/1.52      | ~ m1_pre_topc(sK5,sK2)
% 7.94/1.52      | ~ m1_pre_topc(sK6,sK2)
% 7.94/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 7.94/1.52      | v2_struct_0(X1)
% 7.94/1.52      | v2_struct_0(sK5)
% 7.94/1.52      | v2_struct_0(sK6)
% 7.94/1.52      | v2_struct_0(sK2)
% 7.94/1.52      | ~ l1_pre_topc(X1)
% 7.94/1.52      | ~ l1_pre_topc(sK2)
% 7.94/1.52      | ~ v2_pre_topc(X1)
% 7.94/1.52      | ~ v2_pre_topc(sK2)
% 7.94/1.52      | ~ v1_funct_1(X0) ),
% 7.94/1.52      inference(unflattening,[status(thm)],[c_1016]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_77,negated_conjecture,
% 7.94/1.52      ( ~ v2_struct_0(sK5) ),
% 7.94/1.52      inference(cnf_transformation,[],[f120]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_76,negated_conjecture,
% 7.94/1.52      ( m1_pre_topc(sK5,sK2) ),
% 7.94/1.52      inference(cnf_transformation,[],[f121]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_75,negated_conjecture,
% 7.94/1.52      ( ~ v2_struct_0(sK6) ),
% 7.94/1.52      inference(cnf_transformation,[],[f122]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_74,negated_conjecture,
% 7.94/1.52      ( m1_pre_topc(sK6,sK2) ),
% 7.94/1.52      inference(cnf_transformation,[],[f123]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_1021,plain,
% 7.94/1.52      ( ~ v2_pre_topc(X1)
% 7.94/1.52      | v2_struct_0(X1)
% 7.94/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 7.94/1.52      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 7.94/1.52      | sP1(sK5,sK2,X0,sK6,X1)
% 7.94/1.52      | ~ l1_pre_topc(X1)
% 7.94/1.52      | ~ v1_funct_1(X0) ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_1017,c_86,c_85,c_84,c_77,c_76,c_75,c_74]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_1022,plain,
% 7.94/1.52      ( sP1(sK5,sK2,X0,sK6,X1)
% 7.94/1.52      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 7.94/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 7.94/1.52      | v2_struct_0(X1)
% 7.94/1.52      | ~ l1_pre_topc(X1)
% 7.94/1.52      | ~ v2_pre_topc(X1)
% 7.94/1.52      | ~ v1_funct_1(X0) ),
% 7.94/1.52      inference(renaming,[status(thm)],[c_1021]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_1057,plain,
% 7.94/1.52      ( sP0(X0,X1,X2,X3,X4)
% 7.94/1.52      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_tsep_1(X3,X4,X1),X0)
% 7.94/1.52      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 7.94/1.52      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))
% 7.94/1.52      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 7.94/1.52      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))))
% 7.94/1.52      | v2_struct_0(X6)
% 7.94/1.52      | ~ l1_pre_topc(X6)
% 7.94/1.52      | ~ v2_pre_topc(X6)
% 7.94/1.52      | ~ v1_funct_1(X5)
% 7.94/1.52      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)))
% 7.94/1.52      | X5 != X2
% 7.94/1.52      | X6 != X0
% 7.94/1.52      | sK5 != X4
% 7.94/1.52      | sK6 != X1
% 7.94/1.52      | sK2 != X3 ),
% 7.94/1.52      inference(resolution_lifted,[status(thm)],[c_23,c_1022]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_1058,plain,
% 7.94/1.52      ( sP0(X0,sK6,X1,sK2,sK5)
% 7.94/1.52      | ~ v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
% 7.94/1.52      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 7.94/1.52      | ~ v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))
% 7.94/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 7.94/1.52      | ~ m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
% 7.94/1.52      | v2_struct_0(X0)
% 7.94/1.52      | ~ l1_pre_topc(X0)
% 7.94/1.52      | ~ v2_pre_topc(X0)
% 7.94/1.52      | ~ v1_funct_1(X1)
% 7.94/1.52      | ~ v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) ),
% 7.94/1.52      inference(unflattening,[status(thm)],[c_1057]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4114,plain,
% 7.94/1.52      ( sP0(X0,sK6,X1,sK2,sK5) = iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0) != iProver_top
% 7.94/1.52      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0)) != iProver_top
% 7.94/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0)))) != iProver_top
% 7.94/1.52      | v2_struct_0(X0) = iProver_top
% 7.94/1.52      | l1_pre_topc(X0) != iProver_top
% 7.94/1.52      | v2_pre_topc(X0) != iProver_top
% 7.94/1.52      | v1_funct_1(X1) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_1058]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_73,negated_conjecture,
% 7.94/1.52      ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
% 7.94/1.52      inference(cnf_transformation,[],[f124]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4598,plain,
% 7.94/1.52      ( sP0(X0,sK6,X1,sK2,sK5) = iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,X0,X1,sK2),sK2,X0) != iProver_top
% 7.94/1.52      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 7.94/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 7.94/1.52      | v2_struct_0(X0) = iProver_top
% 7.94/1.52      | l1_pre_topc(X0) != iProver_top
% 7.94/1.52      | v2_pre_topc(X0) != iProver_top
% 7.94/1.52      | v1_funct_1(X1) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,X0,X1,sK2)) != iProver_top ),
% 7.94/1.52      inference(light_normalisation,[status(thm)],[c_4114,c_73]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_20943,plain,
% 7.94/1.52      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v2_struct_0(sK3) = iProver_top
% 7.94/1.52      | l1_pre_topc(sK3) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK3) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
% 7.94/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_20897,c_4598]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_20963,plain,
% 7.94/1.52      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v2_struct_0(sK3) = iProver_top
% 7.94/1.52      | l1_pre_topc(sK3) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK3) != iProver_top
% 7.94/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.52      inference(light_normalisation,[status(thm)],[c_20943,c_20897]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_95,plain,
% 7.94/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_78]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_21,plain,
% 7.94/1.52      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.94/1.52      | ~ sP0(X4,X3,X2,X1,X0)
% 7.94/1.52      | v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) ),
% 7.94/1.52      inference(cnf_transformation,[],[f93]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_1126,plain,
% 7.94/1.52      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.94/1.52      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 7.94/1.52      | v1_funct_2(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))
% 7.94/1.52      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 7.94/1.52      | v2_struct_0(X6)
% 7.94/1.52      | ~ l1_pre_topc(X6)
% 7.94/1.52      | ~ v2_pre_topc(X6)
% 7.94/1.52      | ~ v1_funct_1(X5)
% 7.94/1.52      | X5 != X2
% 7.94/1.52      | X6 != X0
% 7.94/1.52      | sK5 != X4
% 7.94/1.52      | sK6 != X1
% 7.94/1.52      | sK2 != X3 ),
% 7.94/1.52      inference(resolution_lifted,[status(thm)],[c_21,c_1022]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_1127,plain,
% 7.94/1.52      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 7.94/1.52      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))
% 7.94/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 7.94/1.52      | v2_struct_0(X0)
% 7.94/1.52      | ~ l1_pre_topc(X0)
% 7.94/1.52      | ~ v2_pre_topc(X0)
% 7.94/1.52      | ~ v1_funct_1(X1) ),
% 7.94/1.52      inference(unflattening,[status(thm)],[c_1126]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4112,plain,
% 7.94/1.52      ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
% 7.94/1.52      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0)) = iProver_top
% 7.94/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 7.94/1.52      | v2_struct_0(X0) = iProver_top
% 7.94/1.52      | l1_pre_topc(X0) != iProver_top
% 7.94/1.52      | v2_pre_topc(X0) != iProver_top
% 7.94/1.52      | v1_funct_1(X1) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_1127]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4428,plain,
% 7.94/1.52      ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
% 7.94/1.52      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
% 7.94/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 7.94/1.52      | v2_struct_0(X0) = iProver_top
% 7.94/1.52      | l1_pre_topc(X0) != iProver_top
% 7.94/1.52      | v2_pre_topc(X0) != iProver_top
% 7.94/1.52      | v1_funct_1(X1) != iProver_top ),
% 7.94/1.52      inference(light_normalisation,[status(thm)],[c_4112,c_73]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_19,plain,
% 7.94/1.52      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.94/1.52      | ~ sP0(X4,X3,X2,X1,X0)
% 7.94/1.52      | m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) ),
% 7.94/1.52      inference(cnf_transformation,[],[f95]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_1186,plain,
% 7.94/1.52      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.94/1.52      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 7.94/1.52      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 7.94/1.52      | m1_subset_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))))
% 7.94/1.52      | v2_struct_0(X6)
% 7.94/1.52      | ~ l1_pre_topc(X6)
% 7.94/1.52      | ~ v2_pre_topc(X6)
% 7.94/1.52      | ~ v1_funct_1(X5)
% 7.94/1.52      | X5 != X2
% 7.94/1.52      | X6 != X0
% 7.94/1.52      | sK5 != X4
% 7.94/1.52      | sK6 != X1
% 7.94/1.52      | sK2 != X3 ),
% 7.94/1.52      inference(resolution_lifted,[status(thm)],[c_19,c_1022]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_1187,plain,
% 7.94/1.52      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 7.94/1.52      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 7.94/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
% 7.94/1.52      | v2_struct_0(X0)
% 7.94/1.52      | ~ l1_pre_topc(X0)
% 7.94/1.52      | ~ v2_pre_topc(X0)
% 7.94/1.52      | ~ v1_funct_1(X1) ),
% 7.94/1.52      inference(unflattening,[status(thm)],[c_1186]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4110,plain,
% 7.94/1.52      ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
% 7.94/1.52      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 7.94/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0)))) = iProver_top
% 7.94/1.52      | v2_struct_0(X0) = iProver_top
% 7.94/1.52      | l1_pre_topc(X0) != iProver_top
% 7.94/1.52      | v2_pre_topc(X0) != iProver_top
% 7.94/1.52      | v1_funct_1(X1) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_1187]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4445,plain,
% 7.94/1.52      ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
% 7.94/1.52      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 7.94/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) = iProver_top
% 7.94/1.52      | v2_struct_0(X0) = iProver_top
% 7.94/1.52      | l1_pre_topc(X0) != iProver_top
% 7.94/1.52      | v2_pre_topc(X0) != iProver_top
% 7.94/1.52      | v1_funct_1(X1) != iProver_top ),
% 7.94/1.52      inference(light_normalisation,[status(thm)],[c_4110,c_73]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_41,negated_conjecture,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3)
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 7.94/1.52      inference(cnf_transformation,[],[f156]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4138,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_24,plain,
% 7.94/1.52      ( sP0(X0,X1,X2,X3,X4)
% 7.94/1.52      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
% 7.94/1.52      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
% 7.94/1.52      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
% 7.94/1.52      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
% 7.94/1.52      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 7.94/1.52      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
% 7.94/1.52      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
% 7.94/1.52      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
% 7.94/1.52      inference(cnf_transformation,[],[f104]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4152,plain,
% 7.94/1.52      ( sP0(X0,X1,X2,X3,X4) = iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) != iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) != iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) != iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_9376,plain,
% 7.94/1.52      ( sP0(sK3,X0,sK4,sK2,sK6) = iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_4138,c_4152]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_53,negated_conjecture,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3)
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 7.94/1.52      inference(cnf_transformation,[],[f144]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_119,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_49,negated_conjecture,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3)
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
% 7.94/1.52      inference(cnf_transformation,[],[f148]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_123,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_45,negated_conjecture,
% 7.94/1.52      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) ),
% 7.94/1.52      inference(cnf_transformation,[],[f152]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_127,plain,
% 7.94/1.52      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_10562,plain,
% 7.94/1.52      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
% 7.94/1.52      | sP0(sK3,X0,sK4,sK2,sK6) = iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_9376,c_119,c_123,c_127]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_10563,plain,
% 7.94/1.52      ( sP0(sK3,X0,sK4,sK2,sK6) = iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top ),
% 7.94/1.52      inference(renaming,[status(thm)],[c_10562]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_10577,plain,
% 7.94/1.52      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.94/1.52      | sP0(sK3,sK2,sK4,sK2,sK6) = iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v2_struct_0(sK3) = iProver_top
% 7.94/1.52      | l1_pre_topc(sK3) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK3) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
% 7.94/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_4445,c_10563]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_20,plain,
% 7.94/1.52      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.94/1.52      | ~ sP0(X4,X3,X2,X1,X0)
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) ),
% 7.94/1.52      inference(cnf_transformation,[],[f94]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_1156,plain,
% 7.94/1.52      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_tsep_1(X3,X4,X1),X0)
% 7.94/1.52      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 7.94/1.52      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 7.94/1.52      | v2_struct_0(X6)
% 7.94/1.52      | ~ l1_pre_topc(X6)
% 7.94/1.52      | ~ v2_pre_topc(X6)
% 7.94/1.52      | ~ v1_funct_1(X5)
% 7.94/1.52      | X5 != X2
% 7.94/1.52      | X6 != X0
% 7.94/1.52      | sK5 != X4
% 7.94/1.52      | sK6 != X1
% 7.94/1.52      | sK2 != X3 ),
% 7.94/1.52      inference(resolution_lifted,[status(thm)],[c_20,c_1022]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_1157,plain,
% 7.94/1.52      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
% 7.94/1.52      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 7.94/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 7.94/1.52      | v2_struct_0(X0)
% 7.94/1.52      | ~ l1_pre_topc(X0)
% 7.94/1.52      | ~ v2_pre_topc(X0)
% 7.94/1.52      | ~ v1_funct_1(X1) ),
% 7.94/1.52      inference(unflattening,[status(thm)],[c_1156]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4111,plain,
% 7.94/1.52      ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0) = iProver_top
% 7.94/1.52      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 7.94/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 7.94/1.52      | v2_struct_0(X0) = iProver_top
% 7.94/1.52      | l1_pre_topc(X0) != iProver_top
% 7.94/1.52      | v2_pre_topc(X0) != iProver_top
% 7.94/1.52      | v1_funct_1(X1) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_1157]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4411,plain,
% 7.94/1.52      ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,X0,X1,sK2),sK2,X0) = iProver_top
% 7.94/1.52      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 7.94/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 7.94/1.52      | v2_struct_0(X0) = iProver_top
% 7.94/1.52      | l1_pre_topc(X0) != iProver_top
% 7.94/1.52      | v2_pre_topc(X0) != iProver_top
% 7.94/1.52      | v1_funct_1(X1) != iProver_top ),
% 7.94/1.52      inference(light_normalisation,[status(thm)],[c_4111,c_73]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5507,plain,
% 7.94/1.52      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | v2_struct_0(sK3) = iProver_top
% 7.94/1.52      | l1_pre_topc(sK3) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK3) != iProver_top
% 7.94/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_4126,c_4411]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_7087,plain,
% 7.94/1.52      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
% 7.94/1.52      | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_5507,c_90,c_91,c_92,c_93,c_94]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_7088,plain,
% 7.94/1.52      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top ),
% 7.94/1.52      inference(renaming,[status(thm)],[c_7087]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_57,negated_conjecture,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3)
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 7.94/1.52      inference(cnf_transformation,[],[f140]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4134,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_9377,plain,
% 7.94/1.52      ( sP0(sK3,X0,sK4,sK2,sK5) = iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_4134,c_4152]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_69,negated_conjecture,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3)
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
% 7.94/1.52      inference(cnf_transformation,[],[f128]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_103,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_69]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_65,negated_conjecture,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3)
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 7.94/1.52      inference(cnf_transformation,[],[f132]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_107,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_65]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_61,negated_conjecture,
% 7.94/1.52      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) ),
% 7.94/1.52      inference(cnf_transformation,[],[f136]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_111,plain,
% 7.94/1.52      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_10889,plain,
% 7.94/1.52      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
% 7.94/1.52      | sP0(sK3,X0,sK4,sK2,sK5) = iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_9377,c_103,c_107,c_111]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_10890,plain,
% 7.94/1.52      ( sP0(sK3,X0,sK4,sK2,sK5) = iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top ),
% 7.94/1.52      inference(renaming,[status(thm)],[c_10889]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_10902,plain,
% 7.94/1.52      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_4138,c_10890]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_115,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_131,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_8015,plain,
% 7.94/1.52      ( sP0(X0,sK6,sK4,sK2,X1)
% 7.94/1.52      | ~ v5_pre_topc(k2_tmap_1(sK2,X0,sK4,X1),X1,X0)
% 7.94/1.52      | ~ v5_pre_topc(k2_tmap_1(sK2,X0,sK4,sK6),sK6,X0)
% 7.94/1.52      | ~ v1_funct_2(k2_tmap_1(sK2,X0,sK4,X1),u1_struct_0(X1),u1_struct_0(X0))
% 7.94/1.52      | ~ v1_funct_2(k2_tmap_1(sK2,X0,sK4,sK6),u1_struct_0(sK6),u1_struct_0(X0))
% 7.94/1.52      | ~ m1_subset_1(k2_tmap_1(sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 7.94/1.52      | ~ m1_subset_1(k2_tmap_1(sK2,X0,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0))))
% 7.94/1.52      | ~ v1_funct_1(k2_tmap_1(sK2,X0,sK4,X1))
% 7.94/1.52      | ~ v1_funct_1(k2_tmap_1(sK2,X0,sK4,sK6)) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_24]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_10868,plain,
% 7.94/1.52      ( sP0(sK3,sK6,sK4,sK2,sK5)
% 7.94/1.52      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.94/1.52      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.94/1.52      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.94/1.52      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.94/1.52      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.94/1.52      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.94/1.52      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.94/1.52      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_8015]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_10869,plain,
% 7.94/1.52      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_10868]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_10968,plain,
% 7.94/1.52      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_10902,c_103,c_107,c_111,c_115,c_119,c_123,c_127,c_131,
% 7.94/1.52                 c_10869]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_22,plain,
% 7.94/1.52      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.94/1.52      | ~ sP0(X4,X3,X2,X1,X0)
% 7.94/1.52      | v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
% 7.94/1.52      inference(cnf_transformation,[],[f92]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_1096,plain,
% 7.94/1.52      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.94/1.52      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 7.94/1.52      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 7.94/1.52      | v2_struct_0(X6)
% 7.94/1.52      | ~ l1_pre_topc(X6)
% 7.94/1.52      | ~ v2_pre_topc(X6)
% 7.94/1.52      | ~ v1_funct_1(X5)
% 7.94/1.52      | v1_funct_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)))
% 7.94/1.52      | X5 != X2
% 7.94/1.52      | X6 != X0
% 7.94/1.52      | sK5 != X4
% 7.94/1.52      | sK6 != X1
% 7.94/1.52      | sK2 != X3 ),
% 7.94/1.52      inference(resolution_lifted,[status(thm)],[c_22,c_1022]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_1097,plain,
% 7.94/1.52      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 7.94/1.52      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 7.94/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 7.94/1.52      | v2_struct_0(X0)
% 7.94/1.52      | ~ l1_pre_topc(X0)
% 7.94/1.52      | ~ v2_pre_topc(X0)
% 7.94/1.52      | ~ v1_funct_1(X1)
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) ),
% 7.94/1.52      inference(unflattening,[status(thm)],[c_1096]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4113,plain,
% 7.94/1.52      ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
% 7.94/1.52      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 7.94/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 7.94/1.52      | v2_struct_0(X0) = iProver_top
% 7.94/1.52      | l1_pre_topc(X0) != iProver_top
% 7.94/1.52      | v2_pre_topc(X0) != iProver_top
% 7.94/1.52      | v1_funct_1(X1) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_1097]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4394,plain,
% 7.94/1.52      ( sP0(X0,sK6,X1,sK2,sK5) != iProver_top
% 7.94/1.52      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 7.94/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 7.94/1.52      | v2_struct_0(X0) = iProver_top
% 7.94/1.52      | l1_pre_topc(X0) != iProver_top
% 7.94/1.52      | v2_pre_topc(X0) != iProver_top
% 7.94/1.52      | v1_funct_1(X1) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,X0,X1,sK2)) = iProver_top ),
% 7.94/1.52      inference(light_normalisation,[status(thm)],[c_4113,c_73]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5496,plain,
% 7.94/1.52      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | v2_struct_0(sK3) = iProver_top
% 7.94/1.52      | l1_pre_topc(sK3) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK3) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top
% 7.94/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_4126,c_4394]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_7080,plain,
% 7.94/1.52      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top
% 7.94/1.52      | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_5496,c_90,c_91,c_92,c_93,c_94]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_7081,plain,
% 7.94/1.52      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top ),
% 7.94/1.52      inference(renaming,[status(thm)],[c_7080]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_10984,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) = iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_10968,c_7081]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_11255,plain,
% 7.94/1.52      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | sP0(sK3,sK2,sK4,sK2,sK6) = iProver_top ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_10577,c_90,c_91,c_92,c_93,c_94,c_95,c_103,c_107,c_111,
% 7.94/1.52                 c_115,c_119,c_123,c_127,c_131,c_7088,c_10869,c_10984]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_11256,plain,
% 7.94/1.52      ( sP0(sK3,sK2,sK4,sK2,sK6) = iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
% 7.94/1.52      inference(renaming,[status(thm)],[c_11255]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_11263,plain,
% 7.94/1.52      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.94/1.52      | sP0(sK3,sK2,sK4,sK2,sK6) = iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v2_struct_0(sK3) = iProver_top
% 7.94/1.52      | l1_pre_topc(sK3) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK3) != iProver_top
% 7.94/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_4428,c_11256]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_11387,plain,
% 7.94/1.52      ( sP0(sK3,sK2,sK4,sK2,sK6) = iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_11263,c_90,c_91,c_92,c_93,c_94,c_95,c_10968]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_26,plain,
% 7.94/1.52      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) ),
% 7.94/1.52      inference(cnf_transformation,[],[f102]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4150,plain,
% 7.94/1.52      ( sP0(X0,X1,X2,X3,X4) != iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_11397,plain,
% 7.94/1.52      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_11387,c_4150]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5263,plain,
% 7.94/1.52      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_37]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5266,plain,
% 7.94/1.52      ( m1_pre_topc(sK2,sK2) = iProver_top
% 7.94/1.52      | l1_pre_topc(sK2) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_5263]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_16,plain,
% 7.94/1.52      ( ~ v5_pre_topc(X0,X1,X2)
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(X1,X2,X0,X3),X3,X2)
% 7.94/1.52      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.94/1.52      | ~ m1_pre_topc(X3,X1)
% 7.94/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.94/1.52      | v2_struct_0(X1)
% 7.94/1.52      | v2_struct_0(X2)
% 7.94/1.52      | v2_struct_0(X3)
% 7.94/1.52      | ~ l1_pre_topc(X1)
% 7.94/1.52      | ~ l1_pre_topc(X2)
% 7.94/1.52      | ~ v2_pre_topc(X1)
% 7.94/1.52      | ~ v2_pre_topc(X2)
% 7.94/1.52      | ~ v1_funct_1(X0) ),
% 7.94/1.52      inference(cnf_transformation,[],[f90]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4866,plain,
% 7.94/1.52      ( v5_pre_topc(k2_tmap_1(X0,X1,sK4,X2),X2,X1)
% 7.94/1.52      | ~ v5_pre_topc(sK4,X0,X1)
% 7.94/1.52      | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 7.94/1.52      | ~ m1_pre_topc(X2,X0)
% 7.94/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.94/1.52      | v2_struct_0(X0)
% 7.94/1.52      | v2_struct_0(X1)
% 7.94/1.52      | v2_struct_0(X2)
% 7.94/1.52      | ~ l1_pre_topc(X0)
% 7.94/1.52      | ~ l1_pre_topc(X1)
% 7.94/1.52      | ~ v2_pre_topc(X0)
% 7.94/1.52      | ~ v2_pre_topc(X1)
% 7.94/1.52      | ~ v1_funct_1(sK4) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_16]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4967,plain,
% 7.94/1.52      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
% 7.94/1.52      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.94/1.52      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.94/1.52      | ~ m1_pre_topc(X0,sK2)
% 7.94/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.94/1.52      | v2_struct_0(X0)
% 7.94/1.52      | v2_struct_0(sK3)
% 7.94/1.52      | v2_struct_0(sK2)
% 7.94/1.52      | ~ l1_pre_topc(sK3)
% 7.94/1.52      | ~ l1_pre_topc(sK2)
% 7.94/1.52      | ~ v2_pre_topc(sK3)
% 7.94/1.52      | ~ v2_pre_topc(sK2)
% 7.94/1.52      | ~ v1_funct_1(sK4) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_4866]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5932,plain,
% 7.94/1.52      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3)
% 7.94/1.52      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.94/1.52      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.94/1.52      | ~ m1_pre_topc(sK2,sK2)
% 7.94/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.94/1.52      | v2_struct_0(sK3)
% 7.94/1.52      | v2_struct_0(sK2)
% 7.94/1.52      | ~ l1_pre_topc(sK3)
% 7.94/1.52      | ~ l1_pre_topc(sK2)
% 7.94/1.52      | ~ v2_pre_topc(sK3)
% 7.94/1.52      | ~ v2_pre_topc(sK2)
% 7.94/1.52      | ~ v1_funct_1(sK4) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_4967]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5934,plain,
% 7.94/1.52      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.94/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v2_struct_0(sK3) = iProver_top
% 7.94/1.52      | v2_struct_0(sK2) = iProver_top
% 7.94/1.52      | l1_pre_topc(sK3) != iProver_top
% 7.94/1.52      | l1_pre_topc(sK2) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK3) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_5932]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_11539,plain,
% 7.94/1.52      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_11397,c_87,c_88,c_89,c_90,c_91,c_92,c_93,c_94,c_95,
% 7.94/1.52                 c_5266,c_5934]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_20913,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.94/1.52      inference(demodulation,[status(thm)],[c_20897,c_11539]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_27681,plain,
% 7.94/1.52      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_20963,c_90,c_91,c_92,c_93,c_94,c_95,c_20913]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_25,plain,
% 7.94/1.52      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.94/1.52      | m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
% 7.94/1.52      inference(cnf_transformation,[],[f103]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4151,plain,
% 7.94/1.52      ( sP0(X0,X1,X2,X3,X4) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_27686,plain,
% 7.94/1.52      ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_27681,c_4151]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4130,plain,
% 7.94/1.52      ( m1_pre_topc(sK6,sK2) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_74]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_19632,plain,
% 7.94/1.52      ( k2_tmap_1(sK2,sK3,sK4,sK6) = k7_relat_1(sK4,u1_struct_0(sK6)) ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_4130,c_19623]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_27713,plain,
% 7.94/1.52      ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
% 7.94/1.52      inference(light_normalisation,[status(thm)],[c_27686,c_19632]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_29,plain,
% 7.94/1.52      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.94/1.52      | m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) ),
% 7.94/1.52      inference(cnf_transformation,[],[f99]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4147,plain,
% 7.94/1.52      ( sP0(X0,X1,X2,X3,X4) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_27687,plain,
% 7.94/1.52      ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_27681,c_4147]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4128,plain,
% 7.94/1.52      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_76]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_19633,plain,
% 7.94/1.52      ( k2_tmap_1(sK2,sK3,sK4,sK5) = k7_relat_1(sK4,u1_struct_0(sK5)) ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_4128,c_19623]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_27710,plain,
% 7.94/1.52      ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 7.94/1.52      inference(light_normalisation,[status(thm)],[c_27687,c_19633]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_19837,plain,
% 7.94/1.52      ( sP0(sK3,X0,sK4,sK2,sK6) = iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_19632,c_4152]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_19923,plain,
% 7.94/1.52      ( sP0(sK3,X0,sK4,sK2,sK6) = iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
% 7.94/1.52      | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) != iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
% 7.94/1.52      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) != iProver_top ),
% 7.94/1.52      inference(light_normalisation,[status(thm)],[c_19837,c_19632]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4135,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_19711,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) = iProver_top ),
% 7.94/1.52      inference(demodulation,[status(thm)],[c_19632,c_4135]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_98,plain,
% 7.94/1.52      ( v2_struct_0(sK6) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_75]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_99,plain,
% 7.94/1.52      ( m1_pre_topc(sK6,sK2) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_74]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_18,plain,
% 7.94/1.52      ( ~ v5_pre_topc(X0,X1,X2)
% 7.94/1.52      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.94/1.52      | ~ m1_pre_topc(X3,X1)
% 7.94/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.94/1.52      | v2_struct_0(X1)
% 7.94/1.52      | v2_struct_0(X2)
% 7.94/1.52      | v2_struct_0(X3)
% 7.94/1.52      | ~ l1_pre_topc(X1)
% 7.94/1.52      | ~ l1_pre_topc(X2)
% 7.94/1.52      | ~ v2_pre_topc(X1)
% 7.94/1.52      | ~ v2_pre_topc(X2)
% 7.94/1.52      | ~ v1_funct_1(X0)
% 7.94/1.52      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 7.94/1.52      inference(cnf_transformation,[],[f88]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4153,plain,
% 7.94/1.52      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 7.94/1.52      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.94/1.52      | m1_pre_topc(X3,X1) != iProver_top
% 7.94/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.94/1.52      | v2_struct_0(X1) = iProver_top
% 7.94/1.52      | v2_struct_0(X2) = iProver_top
% 7.94/1.52      | v2_struct_0(X3) = iProver_top
% 7.94/1.52      | l1_pre_topc(X1) != iProver_top
% 7.94/1.52      | l1_pre_topc(X2) != iProver_top
% 7.94/1.52      | v2_pre_topc(X1) != iProver_top
% 7.94/1.52      | v2_pre_topc(X2) != iProver_top
% 7.94/1.52      | v1_funct_1(X0) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_9683,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_pre_topc(X0,sK2) != iProver_top
% 7.94/1.52      | v2_struct_0(X0) = iProver_top
% 7.94/1.52      | v2_struct_0(sK3) = iProver_top
% 7.94/1.52      | v2_struct_0(sK2) = iProver_top
% 7.94/1.52      | l1_pre_topc(sK3) != iProver_top
% 7.94/1.52      | l1_pre_topc(sK2) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK3) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) = iProver_top
% 7.94/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_4126,c_4153]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_10280,plain,
% 7.94/1.52      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) = iProver_top
% 7.94/1.52      | v2_struct_0(X0) = iProver_top
% 7.94/1.52      | m1_pre_topc(X0,sK2) != iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_9683,c_87,c_88,c_89,c_90,c_91,c_92,c_93,c_94]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_10281,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.94/1.52      | m1_pre_topc(X0,sK2) != iProver_top
% 7.94/1.52      | v2_struct_0(X0) = iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) = iProver_top ),
% 7.94/1.52      inference(renaming,[status(thm)],[c_10280]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_19843,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.94/1.52      | m1_pre_topc(sK6,sK2) != iProver_top
% 7.94/1.52      | v2_struct_0(sK6) = iProver_top
% 7.94/1.52      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) = iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_19632,c_10281]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_20304,plain,
% 7.94/1.52      ( v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) = iProver_top ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_19711,c_98,c_99,c_19843]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4137,plain,
% 7.94/1.52      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_19710,plain,
% 7.94/1.52      ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) = iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.94/1.52      inference(demodulation,[status(thm)],[c_19632,c_4137]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4155,plain,
% 7.94/1.52      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(X1,X2,X0,X3),X3,X2) = iProver_top
% 7.94/1.52      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.94/1.52      | m1_pre_topc(X3,X1) != iProver_top
% 7.94/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.94/1.52      | v2_struct_0(X1) = iProver_top
% 7.94/1.52      | v2_struct_0(X2) = iProver_top
% 7.94/1.52      | v2_struct_0(X3) = iProver_top
% 7.94/1.52      | l1_pre_topc(X1) != iProver_top
% 7.94/1.52      | l1_pre_topc(X2) != iProver_top
% 7.94/1.52      | v2_pre_topc(X1) != iProver_top
% 7.94/1.52      | v2_pre_topc(X2) != iProver_top
% 7.94/1.52      | v1_funct_1(X0) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_10029,plain,
% 7.94/1.52      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) = iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_pre_topc(X0,sK2) != iProver_top
% 7.94/1.52      | v2_struct_0(X0) = iProver_top
% 7.94/1.52      | v2_struct_0(sK3) = iProver_top
% 7.94/1.52      | v2_struct_0(sK2) = iProver_top
% 7.94/1.52      | l1_pre_topc(sK3) != iProver_top
% 7.94/1.52      | l1_pre_topc(sK2) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK3) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_4126,c_4155]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_10291,plain,
% 7.94/1.52      ( v2_struct_0(X0) = iProver_top
% 7.94/1.52      | m1_pre_topc(X0,sK2) != iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) = iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_10029,c_87,c_88,c_89,c_90,c_91,c_92,c_93,c_94]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_10292,plain,
% 7.94/1.52      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) = iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.94/1.52      | m1_pre_topc(X0,sK2) != iProver_top
% 7.94/1.52      | v2_struct_0(X0) = iProver_top ),
% 7.94/1.52      inference(renaming,[status(thm)],[c_10291]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_19842,plain,
% 7.94/1.52      ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) = iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.94/1.52      | m1_pre_topc(sK6,sK2) != iProver_top
% 7.94/1.52      | v2_struct_0(sK6) = iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_19632,c_10292]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_20336,plain,
% 7.94/1.52      ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) = iProver_top ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_19710,c_98,c_99,c_19842]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4136,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_19709,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.94/1.52      | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
% 7.94/1.52      inference(demodulation,[status(thm)],[c_19632,c_4136]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_17,plain,
% 7.94/1.52      ( ~ v5_pre_topc(X0,X1,X2)
% 7.94/1.52      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.94/1.52      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 7.94/1.52      | ~ m1_pre_topc(X3,X1)
% 7.94/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.94/1.52      | v2_struct_0(X1)
% 7.94/1.52      | v2_struct_0(X2)
% 7.94/1.52      | v2_struct_0(X3)
% 7.94/1.52      | ~ l1_pre_topc(X1)
% 7.94/1.52      | ~ l1_pre_topc(X2)
% 7.94/1.52      | ~ v2_pre_topc(X1)
% 7.94/1.52      | ~ v2_pre_topc(X2)
% 7.94/1.52      | ~ v1_funct_1(X0) ),
% 7.94/1.52      inference(cnf_transformation,[],[f89]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4154,plain,
% 7.94/1.52      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 7.94/1.52      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2)) = iProver_top
% 7.94/1.52      | m1_pre_topc(X3,X1) != iProver_top
% 7.94/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.94/1.52      | v2_struct_0(X1) = iProver_top
% 7.94/1.52      | v2_struct_0(X2) = iProver_top
% 7.94/1.52      | v2_struct_0(X3) = iProver_top
% 7.94/1.52      | l1_pre_topc(X1) != iProver_top
% 7.94/1.52      | l1_pre_topc(X2) != iProver_top
% 7.94/1.52      | v2_pre_topc(X1) != iProver_top
% 7.94/1.52      | v2_pre_topc(X2) != iProver_top
% 7.94/1.52      | v1_funct_1(X0) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_19836,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.94/1.52      | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_pre_topc(sK6,sK2) != iProver_top
% 7.94/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v2_struct_0(sK6) = iProver_top
% 7.94/1.52      | v2_struct_0(sK3) = iProver_top
% 7.94/1.52      | v2_struct_0(sK2) = iProver_top
% 7.94/1.52      | l1_pre_topc(sK3) != iProver_top
% 7.94/1.52      | l1_pre_topc(sK2) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK3) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_19632,c_4154]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_20457,plain,
% 7.94/1.52      ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_19709,c_87,c_88,c_89,c_90,c_91,c_92,c_93,c_94,c_95,
% 7.94/1.52                 c_98,c_99,c_19836]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_21228,plain,
% 7.94/1.52      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top
% 7.94/1.52      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
% 7.94/1.52      | sP0(sK3,X0,sK4,sK2,sK6) = iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_19923,c_87,c_88,c_89,c_90,c_91,c_92,c_93,c_94,c_95,
% 7.94/1.52                 c_98,c_99,c_19709,c_19710,c_19711,c_19836,c_19842,
% 7.94/1.52                 c_19843]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_21229,plain,
% 7.94/1.52      ( sP0(sK3,X0,sK4,sK2,sK6) = iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) != iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) != iProver_top ),
% 7.94/1.52      inference(renaming,[status(thm)],[c_21228]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_21243,plain,
% 7.94/1.52      ( sP0(sK3,sK5,sK4,sK2,sK6) = iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_19633,c_21229]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_21264,plain,
% 7.94/1.52      ( sP0(sK3,sK5,sK4,sK2,sK6) = iProver_top
% 7.94/1.52      | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) != iProver_top
% 7.94/1.52      | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK5))) != iProver_top ),
% 7.94/1.52      inference(light_normalisation,[status(thm)],[c_21243,c_19633]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_39,negated_conjecture,
% 7.94/1.52      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.94/1.52      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.94/1.52      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.94/1.52      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.94/1.52      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.94/1.52      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.94/1.52      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.94/1.52      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.94/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.94/1.52      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.94/1.52      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 7.94/1.52      | ~ v1_funct_1(sK4) ),
% 7.94/1.52      inference(cnf_transformation,[],[f158]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_546,plain,
% 7.94/1.52      ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 7.94/1.52      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.94/1.52      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.94/1.52      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.94/1.52      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.94/1.52      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.94/1.52      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.94/1.52      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.94/1.52      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_39,c_80,c_79,c_78]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_547,negated_conjecture,
% 7.94/1.52      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.94/1.52      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.94/1.52      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.94/1.52      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.94/1.52      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.94/1.52      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.94/1.52      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.94/1.52      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.94/1.52      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 7.94/1.52      inference(renaming,[status(thm)],[c_546]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4117,plain,
% 7.94/1.52      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.94/1.52      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_547]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_19712,plain,
% 7.94/1.52      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.94/1.52      | v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) != iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 7.94/1.52      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) != iProver_top ),
% 7.94/1.52      inference(demodulation,[status(thm)],[c_19632,c_4117]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_96,plain,
% 7.94/1.52      ( v2_struct_0(sK5) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_77]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_97,plain,
% 7.94/1.52      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_76]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4861,plain,
% 7.94/1.52      ( ~ v5_pre_topc(sK4,X0,X1)
% 7.94/1.52      | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 7.94/1.52      | ~ m1_pre_topc(X2,X0)
% 7.94/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.94/1.52      | v2_struct_0(X0)
% 7.94/1.52      | v2_struct_0(X1)
% 7.94/1.52      | v2_struct_0(X2)
% 7.94/1.52      | ~ l1_pre_topc(X0)
% 7.94/1.52      | ~ l1_pre_topc(X1)
% 7.94/1.52      | ~ v2_pre_topc(X0)
% 7.94/1.52      | ~ v2_pre_topc(X1)
% 7.94/1.52      | v1_funct_1(k2_tmap_1(X0,X1,sK4,X2))
% 7.94/1.52      | ~ v1_funct_1(sK4) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_18]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4962,plain,
% 7.94/1.52      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 7.94/1.52      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.94/1.52      | ~ m1_pre_topc(X0,sK2)
% 7.94/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.94/1.52      | v2_struct_0(X0)
% 7.94/1.52      | v2_struct_0(sK3)
% 7.94/1.52      | v2_struct_0(sK2)
% 7.94/1.52      | ~ l1_pre_topc(sK3)
% 7.94/1.52      | ~ l1_pre_topc(sK2)
% 7.94/1.52      | ~ v2_pre_topc(sK3)
% 7.94/1.52      | ~ v2_pre_topc(sK2)
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
% 7.94/1.52      | ~ v1_funct_1(sK4) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_4861]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5046,plain,
% 7.94/1.52      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 7.94/1.52      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.94/1.52      | ~ m1_pre_topc(sK5,sK2)
% 7.94/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.94/1.52      | v2_struct_0(sK5)
% 7.94/1.52      | v2_struct_0(sK3)
% 7.94/1.52      | v2_struct_0(sK2)
% 7.94/1.52      | ~ l1_pre_topc(sK3)
% 7.94/1.52      | ~ l1_pre_topc(sK2)
% 7.94/1.52      | ~ v2_pre_topc(sK3)
% 7.94/1.52      | ~ v2_pre_topc(sK2)
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.94/1.52      | ~ v1_funct_1(sK4) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_4962]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5047,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.94/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v2_struct_0(sK5) = iProver_top
% 7.94/1.52      | v2_struct_0(sK3) = iProver_top
% 7.94/1.52      | v2_struct_0(sK2) = iProver_top
% 7.94/1.52      | l1_pre_topc(sK3) != iProver_top
% 7.94/1.52      | l1_pre_topc(sK2) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK3) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.52      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top
% 7.94/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_5046]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5314,plain,
% 7.94/1.52      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.94/1.52      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.94/1.52      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.94/1.52      | ~ m1_pre_topc(sK5,sK2)
% 7.94/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.94/1.52      | v2_struct_0(sK5)
% 7.94/1.52      | v2_struct_0(sK3)
% 7.94/1.52      | v2_struct_0(sK2)
% 7.94/1.52      | ~ l1_pre_topc(sK3)
% 7.94/1.52      | ~ l1_pre_topc(sK2)
% 7.94/1.52      | ~ v2_pre_topc(sK3)
% 7.94/1.52      | ~ v2_pre_topc(sK2)
% 7.94/1.52      | ~ v1_funct_1(sK4) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_4967]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5315,plain,
% 7.94/1.52      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
% 7.94/1.52      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.94/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v2_struct_0(sK5) = iProver_top
% 7.94/1.52      | v2_struct_0(sK3) = iProver_top
% 7.94/1.52      | v2_struct_0(sK2) = iProver_top
% 7.94/1.52      | l1_pre_topc(sK3) != iProver_top
% 7.94/1.52      | l1_pre_topc(sK2) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK3) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_5314]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4871,plain,
% 7.94/1.52      ( ~ v5_pre_topc(sK4,X0,X1)
% 7.94/1.52      | v1_funct_2(k2_tmap_1(X0,X1,sK4,X2),u1_struct_0(X2),u1_struct_0(X1))
% 7.94/1.52      | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 7.94/1.52      | ~ m1_pre_topc(X2,X0)
% 7.94/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.94/1.52      | v2_struct_0(X0)
% 7.94/1.52      | v2_struct_0(X1)
% 7.94/1.52      | v2_struct_0(X2)
% 7.94/1.52      | ~ l1_pre_topc(X0)
% 7.94/1.52      | ~ l1_pre_topc(X1)
% 7.94/1.52      | ~ v2_pre_topc(X0)
% 7.94/1.52      | ~ v2_pre_topc(X1)
% 7.94/1.52      | ~ v1_funct_1(sK4) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_17]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4972,plain,
% 7.94/1.52      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
% 7.94/1.52      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.94/1.52      | ~ m1_pre_topc(X0,sK2)
% 7.94/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.94/1.52      | v2_struct_0(X0)
% 7.94/1.52      | v2_struct_0(sK3)
% 7.94/1.52      | v2_struct_0(sK2)
% 7.94/1.52      | ~ l1_pre_topc(sK3)
% 7.94/1.52      | ~ l1_pre_topc(sK2)
% 7.94/1.52      | ~ v2_pre_topc(sK3)
% 7.94/1.52      | ~ v2_pre_topc(sK2)
% 7.94/1.52      | ~ v1_funct_1(sK4) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_4871]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5851,plain,
% 7.94/1.52      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.94/1.52      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.94/1.52      | ~ m1_pre_topc(sK5,sK2)
% 7.94/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.94/1.52      | v2_struct_0(sK5)
% 7.94/1.52      | v2_struct_0(sK3)
% 7.94/1.52      | v2_struct_0(sK2)
% 7.94/1.52      | ~ l1_pre_topc(sK3)
% 7.94/1.52      | ~ l1_pre_topc(sK2)
% 7.94/1.52      | ~ v2_pre_topc(sK3)
% 7.94/1.52      | ~ v2_pre_topc(sK2)
% 7.94/1.52      | ~ v1_funct_1(sK4) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_4972]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5852,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.94/1.52      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.94/1.52      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.94/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | v2_struct_0(sK5) = iProver_top
% 7.94/1.52      | v2_struct_0(sK3) = iProver_top
% 7.94/1.52      | v2_struct_0(sK2) = iProver_top
% 7.94/1.52      | l1_pre_topc(sK3) != iProver_top
% 7.94/1.52      | l1_pre_topc(sK2) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK3) != iProver_top
% 7.94/1.52      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_5851]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_20248,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.94/1.52      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_19712,c_87,c_88,c_89,c_90,c_91,c_92,c_93,c_94,c_95,
% 7.94/1.52                 c_96,c_97,c_98,c_99,c_5047,c_5315,c_5852,c_19709,
% 7.94/1.52                 c_19710,c_19711,c_19836,c_19842,c_19843]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_20252,plain,
% 7.94/1.52      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.94/1.52      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top ),
% 7.94/1.52      inference(light_normalisation,[status(thm)],[c_20248,c_19633]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_21422,plain,
% 7.94/1.52      ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_21264,c_20252,c_20913]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_21423,plain,
% 7.94/1.52      ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.94/1.52      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top ),
% 7.94/1.52      inference(renaming,[status(thm)],[c_21422]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(contradiction,plain,
% 7.94/1.52      ( $false ),
% 7.94/1.52      inference(minisat,[status(thm)],[c_27713,c_27710,c_21423]) ).
% 7.94/1.52  
% 7.94/1.52  
% 7.94/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.94/1.52  
% 7.94/1.52  ------                               Statistics
% 7.94/1.52  
% 7.94/1.52  ------ General
% 7.94/1.52  
% 7.94/1.52  abstr_ref_over_cycles:                  0
% 7.94/1.52  abstr_ref_under_cycles:                 0
% 7.94/1.52  gc_basic_clause_elim:                   0
% 7.94/1.52  forced_gc_time:                         0
% 7.94/1.52  parsing_time:                           0.014
% 7.94/1.52  unif_index_cands_time:                  0.
% 7.94/1.52  unif_index_add_time:                    0.
% 7.94/1.52  orderings_time:                         0.
% 7.94/1.52  out_proof_time:                         0.028
% 7.94/1.52  total_time:                             0.826
% 7.94/1.52  num_of_symbols:                         59
% 7.94/1.52  num_of_terms:                           18309
% 7.94/1.52  
% 7.94/1.52  ------ Preprocessing
% 7.94/1.52  
% 7.94/1.52  num_of_splits:                          0
% 7.94/1.52  num_of_split_atoms:                     0
% 7.94/1.52  num_of_reused_defs:                     0
% 7.94/1.52  num_eq_ax_congr_red:                    34
% 7.94/1.52  num_of_sem_filtered_clauses:            1
% 7.94/1.52  num_of_subtypes:                        0
% 7.94/1.52  monotx_restored_types:                  0
% 7.94/1.52  sat_num_of_epr_types:                   0
% 7.94/1.52  sat_num_of_non_cyclic_types:            0
% 7.94/1.52  sat_guarded_non_collapsed_types:        0
% 7.94/1.52  num_pure_diseq_elim:                    0
% 7.94/1.52  simp_replaced_by:                       0
% 7.94/1.52  res_preprocessed:                       278
% 7.94/1.52  prep_upred:                             0
% 7.94/1.52  prep_unflattend:                        148
% 7.94/1.52  smt_new_axioms:                         0
% 7.94/1.52  pred_elim_cands:                        11
% 7.94/1.52  pred_elim:                              3
% 7.94/1.52  pred_elim_cl:                           3
% 7.94/1.52  pred_elim_cycles:                       5
% 7.94/1.52  merged_defs:                            8
% 7.94/1.52  merged_defs_ncl:                        0
% 7.94/1.52  bin_hyper_res:                          9
% 7.94/1.52  prep_cycles:                            4
% 7.94/1.52  pred_elim_time:                         0.05
% 7.94/1.52  splitting_time:                         0.
% 7.94/1.52  sem_filter_time:                        0.
% 7.94/1.52  monotx_time:                            0.001
% 7.94/1.52  subtype_inf_time:                       0.
% 7.94/1.52  
% 7.94/1.52  ------ Problem properties
% 7.94/1.52  
% 7.94/1.52  clauses:                                59
% 7.94/1.52  conjectures:                            23
% 7.94/1.52  epr:                                    18
% 7.94/1.52  horn:                                   38
% 7.94/1.52  ground:                                 23
% 7.94/1.52  unary:                                  16
% 7.94/1.52  binary:                                 19
% 7.94/1.52  lits:                                   224
% 7.94/1.52  lits_eq:                                6
% 7.94/1.52  fd_pure:                                0
% 7.94/1.52  fd_pseudo:                              0
% 7.94/1.52  fd_cond:                                0
% 7.94/1.52  fd_pseudo_cond:                         1
% 7.94/1.52  ac_symbols:                             0
% 7.94/1.52  
% 7.94/1.52  ------ Propositional Solver
% 7.94/1.52  
% 7.94/1.52  prop_solver_calls:                      32
% 7.94/1.52  prop_fast_solver_calls:                 4388
% 7.94/1.52  smt_solver_calls:                       0
% 7.94/1.52  smt_fast_solver_calls:                  0
% 7.94/1.52  prop_num_of_clauses:                    7584
% 7.94/1.52  prop_preprocess_simplified:             17999
% 7.94/1.52  prop_fo_subsumed:                       499
% 7.94/1.52  prop_solver_time:                       0.
% 7.94/1.52  smt_solver_time:                        0.
% 7.94/1.52  smt_fast_solver_time:                   0.
% 7.94/1.52  prop_fast_solver_time:                  0.
% 7.94/1.52  prop_unsat_core_time:                   0.001
% 7.94/1.52  
% 7.94/1.52  ------ QBF
% 7.94/1.52  
% 7.94/1.52  qbf_q_res:                              0
% 7.94/1.52  qbf_num_tautologies:                    0
% 7.94/1.52  qbf_prep_cycles:                        0
% 7.94/1.52  
% 7.94/1.52  ------ BMC1
% 7.94/1.52  
% 7.94/1.52  bmc1_current_bound:                     -1
% 7.94/1.52  bmc1_last_solved_bound:                 -1
% 7.94/1.52  bmc1_unsat_core_size:                   -1
% 7.94/1.52  bmc1_unsat_core_parents_size:           -1
% 7.94/1.52  bmc1_merge_next_fun:                    0
% 7.94/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.94/1.52  
% 7.94/1.52  ------ Instantiation
% 7.94/1.52  
% 7.94/1.52  inst_num_of_clauses:                    2153
% 7.94/1.52  inst_num_in_passive:                    72
% 7.94/1.52  inst_num_in_active:                     1225
% 7.94/1.52  inst_num_in_unprocessed:                857
% 7.94/1.52  inst_num_of_loops:                      1410
% 7.94/1.52  inst_num_of_learning_restarts:          0
% 7.94/1.52  inst_num_moves_active_passive:          180
% 7.94/1.52  inst_lit_activity:                      0
% 7.94/1.52  inst_lit_activity_moves:                1
% 7.94/1.52  inst_num_tautologies:                   0
% 7.94/1.52  inst_num_prop_implied:                  0
% 7.94/1.52  inst_num_existing_simplified:           0
% 7.94/1.52  inst_num_eq_res_simplified:             0
% 7.94/1.52  inst_num_child_elim:                    0
% 7.94/1.52  inst_num_of_dismatching_blockings:      1442
% 7.94/1.52  inst_num_of_non_proper_insts:           3187
% 7.94/1.52  inst_num_of_duplicates:                 0
% 7.94/1.52  inst_inst_num_from_inst_to_res:         0
% 7.94/1.52  inst_dismatching_checking_time:         0.
% 7.94/1.52  
% 7.94/1.52  ------ Resolution
% 7.94/1.52  
% 7.94/1.52  res_num_of_clauses:                     0
% 7.94/1.52  res_num_in_passive:                     0
% 7.94/1.52  res_num_in_active:                      0
% 7.94/1.52  res_num_of_loops:                       282
% 7.94/1.52  res_forward_subset_subsumed:            167
% 7.94/1.52  res_backward_subset_subsumed:           8
% 7.94/1.52  res_forward_subsumed:                   0
% 7.94/1.52  res_backward_subsumed:                  0
% 7.94/1.52  res_forward_subsumption_resolution:     0
% 7.94/1.52  res_backward_subsumption_resolution:    0
% 7.94/1.52  res_clause_to_clause_subsumption:       3212
% 7.94/1.52  res_orphan_elimination:                 0
% 7.94/1.52  res_tautology_del:                      309
% 7.94/1.52  res_num_eq_res_simplified:              0
% 7.94/1.52  res_num_sel_changes:                    0
% 7.94/1.52  res_moves_from_active_to_pass:          0
% 7.94/1.52  
% 7.94/1.52  ------ Superposition
% 7.94/1.52  
% 7.94/1.52  sup_time_total:                         0.
% 7.94/1.52  sup_time_generating:                    0.
% 7.94/1.52  sup_time_sim_full:                      0.
% 7.94/1.52  sup_time_sim_immed:                     0.
% 7.94/1.52  
% 7.94/1.52  sup_num_of_clauses:                     494
% 7.94/1.52  sup_num_in_active:                      220
% 7.94/1.52  sup_num_in_passive:                     274
% 7.94/1.52  sup_num_of_loops:                       280
% 7.94/1.52  sup_fw_superposition:                   388
% 7.94/1.52  sup_bw_superposition:                   472
% 7.94/1.52  sup_immediate_simplified:               265
% 7.94/1.52  sup_given_eliminated:                   0
% 7.94/1.52  comparisons_done:                       0
% 7.94/1.52  comparisons_avoided:                    0
% 7.94/1.52  
% 7.94/1.52  ------ Simplifications
% 7.94/1.52  
% 7.94/1.52  
% 7.94/1.52  sim_fw_subset_subsumed:                 123
% 7.94/1.52  sim_bw_subset_subsumed:                 29
% 7.94/1.52  sim_fw_subsumed:                        38
% 7.94/1.52  sim_bw_subsumed:                        2
% 7.94/1.52  sim_fw_subsumption_res:                 8
% 7.94/1.52  sim_bw_subsumption_res:                 0
% 7.94/1.52  sim_tautology_del:                      45
% 7.94/1.52  sim_eq_tautology_del:                   14
% 7.94/1.52  sim_eq_res_simp:                        0
% 7.94/1.52  sim_fw_demodulated:                     7
% 7.94/1.52  sim_bw_demodulated:                     54
% 7.94/1.52  sim_light_normalised:                   119
% 7.94/1.52  sim_joinable_taut:                      0
% 7.94/1.52  sim_joinable_simp:                      0
% 7.94/1.52  sim_ac_normalised:                      0
% 7.94/1.52  sim_smt_subsumption:                    0
% 7.94/1.52  
%------------------------------------------------------------------------------
