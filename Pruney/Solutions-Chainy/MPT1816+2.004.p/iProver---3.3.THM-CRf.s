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
% DateTime   : Thu Dec  3 12:24:19 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :  263 (3082 expanded)
%              Number of clauses        :  177 ( 655 expanded)
%              Number of leaves         :   18 (1065 expanded)
%              Depth                    :   27
%              Number of atoms          : 1891 (94799 expanded)
%              Number of equality atoms :  479 (3679 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal clause size      :   78 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f41,f46,f45,f44,f43,f42])).

fof(f121,plain,
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
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f81,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f82,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,(
    m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f77,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f78,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f32,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
      <=> sP0(X1,X3,X4,X0,X2) )
      | ~ sP1(X2,X0,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0)
      | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
      | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
      | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f36])).

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
    inference(ennf_transformation,[],[f9])).

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

fof(f31,plain,(
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

fof(f33,plain,(
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
    inference(definition_folding,[],[f27,f32,f31])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f88,plain,(
    r4_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f83,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f85,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f87,plain,(
    k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f73,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(flattening,[],[f22])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f99,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f115,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f119,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2673,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | m1_subset_1(k2_tmap_1(X0_54,X1_54,X0_55,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | ~ l1_struct_0(X2_54)
    | ~ l1_struct_0(X1_54)
    | ~ l1_struct_0(X0_54)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3516,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_54,X1_54,X0_55,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) = iProver_top
    | l1_struct_0(X2_54) != iProver_top
    | l1_struct_0(X1_54) != iProver_top
    | l1_struct_0(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2673])).

cnf(c_26,negated_conjecture,
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
    inference(cnf_transformation,[],[f121])).

cnf(c_67,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_66,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_65,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_478,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_67,c_66,c_65])).

cnf(c_479,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(renaming,[status(thm)],[c_478])).

cnf(c_2638,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(subtyping,[status(esa)],[c_479])).

cnf(c_3550,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2638])).

cnf(c_71,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_76,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_68,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_79,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_68])).

cnf(c_80,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_67])).

cnf(c_81,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66])).

cnf(c_82,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_174,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_176,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_174])).

cnf(c_480,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_63,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_816,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK5 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_63])).

cnf(c_817,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_816])).

cnf(c_818,plain,
    ( l1_pre_topc(sK5) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_817])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2671,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ l1_struct_0(X2_54)
    | ~ l1_struct_0(X1_54)
    | ~ l1_struct_0(X0_54)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k2_tmap_1(X0_54,X1_54,X0_55,X2_54)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_3659,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2671])).

cnf(c_3660,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3659])).

cnf(c_2676,plain,
    ( ~ l1_pre_topc(X0_54)
    | l1_struct_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3731,plain,
    ( ~ l1_pre_topc(sK5)
    | l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2676])).

cnf(c_3732,plain,
    ( l1_pre_topc(sK5) != iProver_top
    | l1_struct_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3731])).

cnf(c_3823,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2676])).

cnf(c_3824,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3823])).

cnf(c_3978,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3550,c_76,c_79,c_80,c_81,c_82,c_176,c_480,c_818,c_3660,c_3732,c_3824])).

cnf(c_3979,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3978])).

cnf(c_5188,plain,
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
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3516,c_3979])).

cnf(c_61,negated_conjecture,
    ( m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_805,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK6 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_61])).

cnf(c_806,plain,
    ( l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_805])).

cnf(c_807,plain,
    ( l1_pre_topc(sK6) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_806])).

cnf(c_4035,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(X0_54)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2671])).

cnf(c_4054,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK6)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4035])).

cnf(c_4055,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4054])).

cnf(c_4099,plain,
    ( ~ l1_pre_topc(sK6)
    | l1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2676])).

cnf(c_4100,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_struct_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4099])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2672,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | v1_funct_2(k2_tmap_1(X0_54,X1_54,X0_55,X2_54),u1_struct_0(X2_54),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ l1_struct_0(X2_54)
    | ~ l1_struct_0(X1_54)
    | ~ l1_struct_0(X0_54)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_4144,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_54),u1_struct_0(X0_54),u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(X0_54)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2672])).

cnf(c_4509,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4144])).

cnf(c_4510,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4509])).

cnf(c_4457,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(X0_54)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2673])).

cnf(c_4955,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4457])).

cnf(c_4956,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4955])).

cnf(c_5611,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5188,c_76,c_79,c_80,c_81,c_82,c_176,c_480,c_807,c_818,c_3660,c_3732,c_3824,c_4055,c_4100,c_4510,c_4956])).

cnf(c_5612,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5611])).

cnf(c_5616,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3516,c_5612])).

cnf(c_70,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_77,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_70])).

cnf(c_69,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_78,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_2647,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_65])).

cnf(c_3541,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2647])).

cnf(c_3517,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_54,X1_54,X0_55,X2_54),u1_struct_0(X2_54),u1_struct_0(X1_54)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | l1_struct_0(X2_54) != iProver_top
    | l1_struct_0(X1_54) != iProver_top
    | l1_struct_0(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2672])).

cnf(c_14,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | sP0(X4,X3,X2,X1,X0)
    | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
    | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
    | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
    | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,plain,
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
    inference(cnf_transformation,[],[f72])).

cnf(c_59,negated_conjecture,
    ( r4_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_762,plain,
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
    inference(resolution_lifted,[status(thm)],[c_24,c_59])).

cnf(c_763,plain,
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
    inference(unflattening,[status(thm)],[c_762])).

cnf(c_73,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_72,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_64,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_62,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_767,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | sP1(sK5,sK2,X0,sK6,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_763,c_73,c_72,c_71,c_64,c_63,c_62,c_61])).

cnf(c_768,plain,
    ( sP1(sK5,sK2,X0,sK6,X1)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_767])).

cnf(c_955,plain,
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
    inference(resolution_lifted,[status(thm)],[c_14,c_768])).

cnf(c_956,plain,
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
    inference(unflattening,[status(thm)],[c_955])).

cnf(c_2636,plain,
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
    inference(subtyping,[status(esa)],[c_956])).

cnf(c_3552,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_2636])).

cnf(c_60,negated_conjecture,
    ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2652,negated_conjecture,
    ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(subtyping,[status(esa)],[c_60])).

cnf(c_3561,plain,
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
    inference(light_normalisation,[status(thm)],[c_3552,c_2652])).

cnf(c_5193,plain,
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
    inference(superposition,[status(thm)],[c_3516,c_3561])).

cnf(c_2725,plain,
    ( l1_pre_topc(X0_54) != iProver_top
    | l1_struct_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2676])).

cnf(c_6906,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_5193,c_76,c_2725,c_3824])).

cnf(c_6912,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_struct_0(X0_54) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3517,c_6906])).

cnf(c_8657,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6912,c_76,c_2725,c_3824])).

cnf(c_8663,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3541,c_8657])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_0,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_742,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_2,c_0])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_746,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_742,c_2,c_1,c_0])).

cnf(c_2637,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | k7_relat_1(X0_55,X0_56) = X0_55 ),
    inference(subtyping,[status(esa)],[c_746])).

cnf(c_3551,plain,
    ( k7_relat_1(X0_55,X0_56) = X0_55
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2637])).

cnf(c_6593,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK4 ),
    inference(superposition,[status(thm)],[c_3541,c_3551])).

cnf(c_25,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2661,plain,
    ( m1_pre_topc(X0_54,X0_54)
    | ~ l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_3528,plain,
    ( m1_pre_topc(X0_54,X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2661])).

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
    inference(cnf_transformation,[],[f54])).

cnf(c_2674,plain,
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

cnf(c_3515,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_55,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_55,X2_54)
    | v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2674])).

cnf(c_4652,plain,
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
    inference(superposition,[status(thm)],[c_3541,c_3515])).

cnf(c_74,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_75,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_72])).

cnf(c_5874,plain,
    ( m1_pre_topc(X0_54,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK3,sK4,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4652,c_74,c_75,c_76,c_77,c_78,c_79,c_80,c_81])).

cnf(c_5875,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK3,sK4,X0_54)
    | m1_pre_topc(X0_54,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5874])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2677,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_funct_1(X0_55)
    | k2_partfun1(X0_56,X1_56,X0_55,X2_56) = k7_relat_1(X0_55,X2_56) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_3512,plain,
    ( k2_partfun1(X0_56,X1_56,X0_55,X2_56) = k7_relat_1(X0_55,X2_56)
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2677])).

cnf(c_3973,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_56) = k7_relat_1(sK4,X0_56)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3541,c_3512])).

cnf(c_5009,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_56) = k7_relat_1(sK4,X0_56) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3973,c_80])).

cnf(c_5880,plain,
    ( k2_tmap_1(sK2,sK3,sK4,X0_54) = k7_relat_1(sK4,u1_struct_0(X0_54))
    | m1_pre_topc(X0_54,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5875,c_5009])).

cnf(c_5886,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2))
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3528,c_5880])).

cnf(c_6166,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5886,c_76])).

cnf(c_6686,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4 ),
    inference(demodulation,[status(thm)],[c_6593,c_6166])).

cnf(c_8666,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8663,c_6686])).

cnf(c_21,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2664,plain,
    ( ~ sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
    | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),X3_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_3924,plain,
    ( ~ sP0(sK3,X0_54,sK4,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
    inference(instantiation,[status(thm)],[c_2664])).

cnf(c_9277,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
    inference(instantiation,[status(thm)],[c_3924])).

cnf(c_9281,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9277])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2668,plain,
    ( ~ sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
    | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),X1_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_4477,plain,
    ( ~ sP0(sK3,X0_54,sK4,sK2,X1_54)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_54),X0_54,sK3) ),
    inference(instantiation,[status(thm)],[c_2668])).

cnf(c_9287,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
    inference(instantiation,[status(thm)],[c_4477])).

cnf(c_9289,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9287])).

cnf(c_9400,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5616,c_76,c_77,c_78,c_79,c_80,c_81,c_82,c_176,c_807,c_3824,c_4100,c_8666,c_9281,c_9289])).

cnf(c_48,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_98,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_32,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_114,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_28,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_118,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_15,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2670,plain,
    ( sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
    | ~ v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),X1_54,X0_54)
    | ~ v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),X3_54,X0_54)
    | ~ v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),u1_struct_0(X1_54),u1_struct_0(X0_54))
    | ~ v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),u1_struct_0(X3_54),u1_struct_0(X0_54))
    | ~ m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54))))
    | ~ m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X0_54))))
    | ~ v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_55,X1_54))
    | ~ v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_55,X3_54)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_3695,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5)
    | ~ v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK5),sK5,X0_54)
    | ~ v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK6),sK6,X0_54)
    | ~ v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK5),u1_struct_0(sK5),u1_struct_0(X0_54))
    | ~ v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK6),u1_struct_0(sK6),u1_struct_0(X0_54))
    | ~ m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54))))
    | ~ m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_54))))
    | ~ v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK6)) ),
    inference(instantiation,[status(thm)],[c_2670])).

cnf(c_3696,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK5),sK5,X0_54) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK6),sK6,X0_54) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK5),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK6),u1_struct_0(sK6),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3695])).

cnf(c_3698,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3696])).

cnf(c_10,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1084,plain,
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
    inference(resolution_lifted,[status(thm)],[c_10,c_768])).

cnf(c_1085,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_1084])).

cnf(c_2632,plain,
    ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
    | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54))))
    | v2_struct_0(X0_54)
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_1085])).

cnf(c_3556,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54)))) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2632])).

cnf(c_3560,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3556,c_2652])).

cnf(c_11,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1054,plain,
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
    inference(resolution_lifted,[status(thm)],[c_11,c_768])).

cnf(c_1055,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_1054])).

cnf(c_2633,plain,
    ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_54)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
    | v2_struct_0(X0_54)
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_1055])).

cnf(c_3555,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_54) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2633])).

cnf(c_3558,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3555,c_2652])).

cnf(c_4558,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | sP0(X0_54,sK6,k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2),sK2,X0_54) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3560,c_3558])).

cnf(c_12,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1024,plain,
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
    inference(resolution_lifted,[status(thm)],[c_12,c_768])).

cnf(c_1025,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_1024])).

cnf(c_2634,plain,
    ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
    | v2_struct_0(X0_54)
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_1025])).

cnf(c_3554,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2634])).

cnf(c_3559,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3554,c_2652])).

cnf(c_13,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_994,plain,
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
    inference(resolution_lifted,[status(thm)],[c_13,c_768])).

cnf(c_995,plain,
    ( ~ sP0(X0,sK6,X1,sK2,sK5)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X1)
    | v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(unflattening,[status(thm)],[c_994])).

cnf(c_2635,plain,
    ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
    | v2_struct_0(X0_54)
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(subtyping,[status(esa)],[c_995])).

cnf(c_3553,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2635])).

cnf(c_3557,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3553,c_2652])).

cnf(c_6989,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | sP0(X0_54,sK6,k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2),sK2,X0_54) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4558,c_3559,c_3557])).

cnf(c_6990,plain,
    ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
    | sP0(X0_54,sK6,k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_54,k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2),sK2,X0_54) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_6989])).

cnf(c_9183,plain,
    ( sP0(sK3,sK6,k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK5) != iProver_top
    | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6686,c_6990])).

cnf(c_9199,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9183,c_6686])).

cnf(c_9404,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9400,c_76,c_77,c_78,c_79,c_80,c_81,c_82,c_98,c_114,c_118,c_176,c_807,c_818,c_3660,c_3698,c_3732,c_3824,c_4055,c_4100,c_4510,c_4956,c_9199])).

cnf(c_2651,negated_conjecture,
    ( m1_pre_topc(sK6,sK2) ),
    inference(subtyping,[status(esa)],[c_61])).

cnf(c_3537,plain,
    ( m1_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2651])).

cnf(c_5884,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK6) = k7_relat_1(sK4,u1_struct_0(sK6)) ),
    inference(superposition,[status(thm)],[c_3537,c_5880])).

cnf(c_9408,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9404,c_5884])).

cnf(c_5980,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5884,c_3517])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9408,c_5980,c_4100,c_3824,c_807,c_176,c_82,c_81,c_80,c_79,c_76])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:28:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.67/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/1.50  
% 7.67/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.67/1.50  
% 7.67/1.50  ------  iProver source info
% 7.67/1.50  
% 7.67/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.67/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.67/1.50  git: non_committed_changes: false
% 7.67/1.50  git: last_make_outside_of_git: false
% 7.67/1.50  
% 7.67/1.50  ------ 
% 7.67/1.50  
% 7.67/1.50  ------ Input Options
% 7.67/1.50  
% 7.67/1.50  --out_options                           all
% 7.67/1.50  --tptp_safe_out                         true
% 7.67/1.50  --problem_path                          ""
% 7.67/1.50  --include_path                          ""
% 7.67/1.50  --clausifier                            res/vclausify_rel
% 7.67/1.50  --clausifier_options                    ""
% 7.67/1.50  --stdin                                 false
% 7.67/1.50  --stats_out                             all
% 7.67/1.50  
% 7.67/1.50  ------ General Options
% 7.67/1.50  
% 7.67/1.50  --fof                                   false
% 7.67/1.50  --time_out_real                         305.
% 7.67/1.50  --time_out_virtual                      -1.
% 7.67/1.50  --symbol_type_check                     false
% 7.67/1.50  --clausify_out                          false
% 7.67/1.50  --sig_cnt_out                           false
% 7.67/1.50  --trig_cnt_out                          false
% 7.67/1.50  --trig_cnt_out_tolerance                1.
% 7.67/1.50  --trig_cnt_out_sk_spl                   false
% 7.67/1.50  --abstr_cl_out                          false
% 7.67/1.50  
% 7.67/1.50  ------ Global Options
% 7.67/1.50  
% 7.67/1.50  --schedule                              default
% 7.67/1.50  --add_important_lit                     false
% 7.67/1.50  --prop_solver_per_cl                    1000
% 7.67/1.50  --min_unsat_core                        false
% 7.67/1.50  --soft_assumptions                      false
% 7.67/1.50  --soft_lemma_size                       3
% 7.67/1.50  --prop_impl_unit_size                   0
% 7.67/1.50  --prop_impl_unit                        []
% 7.67/1.50  --share_sel_clauses                     true
% 7.67/1.50  --reset_solvers                         false
% 7.67/1.50  --bc_imp_inh                            [conj_cone]
% 7.67/1.50  --conj_cone_tolerance                   3.
% 7.67/1.50  --extra_neg_conj                        none
% 7.67/1.50  --large_theory_mode                     true
% 7.67/1.50  --prolific_symb_bound                   200
% 7.67/1.50  --lt_threshold                          2000
% 7.67/1.50  --clause_weak_htbl                      true
% 7.67/1.50  --gc_record_bc_elim                     false
% 7.67/1.50  
% 7.67/1.50  ------ Preprocessing Options
% 7.67/1.50  
% 7.67/1.50  --preprocessing_flag                    true
% 7.67/1.50  --time_out_prep_mult                    0.1
% 7.67/1.50  --splitting_mode                        input
% 7.67/1.50  --splitting_grd                         true
% 7.67/1.50  --splitting_cvd                         false
% 7.67/1.50  --splitting_cvd_svl                     false
% 7.67/1.50  --splitting_nvd                         32
% 7.67/1.50  --sub_typing                            true
% 7.67/1.50  --prep_gs_sim                           true
% 7.67/1.50  --prep_unflatten                        true
% 7.67/1.50  --prep_res_sim                          true
% 7.67/1.50  --prep_upred                            true
% 7.67/1.50  --prep_sem_filter                       exhaustive
% 7.67/1.50  --prep_sem_filter_out                   false
% 7.67/1.50  --pred_elim                             true
% 7.67/1.50  --res_sim_input                         true
% 7.67/1.50  --eq_ax_congr_red                       true
% 7.67/1.50  --pure_diseq_elim                       true
% 7.67/1.50  --brand_transform                       false
% 7.67/1.50  --non_eq_to_eq                          false
% 7.67/1.50  --prep_def_merge                        true
% 7.67/1.50  --prep_def_merge_prop_impl              false
% 7.67/1.50  --prep_def_merge_mbd                    true
% 7.67/1.50  --prep_def_merge_tr_red                 false
% 7.67/1.50  --prep_def_merge_tr_cl                  false
% 7.67/1.50  --smt_preprocessing                     true
% 7.67/1.50  --smt_ac_axioms                         fast
% 7.67/1.50  --preprocessed_out                      false
% 7.67/1.50  --preprocessed_stats                    false
% 7.67/1.50  
% 7.67/1.50  ------ Abstraction refinement Options
% 7.67/1.50  
% 7.67/1.50  --abstr_ref                             []
% 7.67/1.50  --abstr_ref_prep                        false
% 7.67/1.50  --abstr_ref_until_sat                   false
% 7.67/1.50  --abstr_ref_sig_restrict                funpre
% 7.67/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.67/1.50  --abstr_ref_under                       []
% 7.67/1.50  
% 7.67/1.50  ------ SAT Options
% 7.67/1.50  
% 7.67/1.50  --sat_mode                              false
% 7.67/1.50  --sat_fm_restart_options                ""
% 7.67/1.50  --sat_gr_def                            false
% 7.67/1.50  --sat_epr_types                         true
% 7.67/1.50  --sat_non_cyclic_types                  false
% 7.67/1.50  --sat_finite_models                     false
% 7.67/1.50  --sat_fm_lemmas                         false
% 7.67/1.50  --sat_fm_prep                           false
% 7.67/1.50  --sat_fm_uc_incr                        true
% 7.67/1.50  --sat_out_model                         small
% 7.67/1.50  --sat_out_clauses                       false
% 7.67/1.50  
% 7.67/1.50  ------ QBF Options
% 7.67/1.50  
% 7.67/1.50  --qbf_mode                              false
% 7.67/1.50  --qbf_elim_univ                         false
% 7.67/1.50  --qbf_dom_inst                          none
% 7.67/1.50  --qbf_dom_pre_inst                      false
% 7.67/1.50  --qbf_sk_in                             false
% 7.67/1.50  --qbf_pred_elim                         true
% 7.67/1.50  --qbf_split                             512
% 7.67/1.50  
% 7.67/1.50  ------ BMC1 Options
% 7.67/1.50  
% 7.67/1.50  --bmc1_incremental                      false
% 7.67/1.50  --bmc1_axioms                           reachable_all
% 7.67/1.50  --bmc1_min_bound                        0
% 7.67/1.50  --bmc1_max_bound                        -1
% 7.67/1.50  --bmc1_max_bound_default                -1
% 7.67/1.50  --bmc1_symbol_reachability              true
% 7.67/1.50  --bmc1_property_lemmas                  false
% 7.67/1.50  --bmc1_k_induction                      false
% 7.67/1.50  --bmc1_non_equiv_states                 false
% 7.67/1.50  --bmc1_deadlock                         false
% 7.67/1.50  --bmc1_ucm                              false
% 7.67/1.50  --bmc1_add_unsat_core                   none
% 7.67/1.50  --bmc1_unsat_core_children              false
% 7.67/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.67/1.50  --bmc1_out_stat                         full
% 7.67/1.50  --bmc1_ground_init                      false
% 7.67/1.50  --bmc1_pre_inst_next_state              false
% 7.67/1.50  --bmc1_pre_inst_state                   false
% 7.67/1.50  --bmc1_pre_inst_reach_state             false
% 7.67/1.50  --bmc1_out_unsat_core                   false
% 7.67/1.50  --bmc1_aig_witness_out                  false
% 7.67/1.50  --bmc1_verbose                          false
% 7.67/1.50  --bmc1_dump_clauses_tptp                false
% 7.67/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.67/1.50  --bmc1_dump_file                        -
% 7.67/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.67/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.67/1.50  --bmc1_ucm_extend_mode                  1
% 7.67/1.50  --bmc1_ucm_init_mode                    2
% 7.67/1.50  --bmc1_ucm_cone_mode                    none
% 7.67/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.67/1.50  --bmc1_ucm_relax_model                  4
% 7.67/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.67/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.67/1.50  --bmc1_ucm_layered_model                none
% 7.67/1.50  --bmc1_ucm_max_lemma_size               10
% 7.67/1.50  
% 7.67/1.50  ------ AIG Options
% 7.67/1.50  
% 7.67/1.50  --aig_mode                              false
% 7.67/1.50  
% 7.67/1.50  ------ Instantiation Options
% 7.67/1.50  
% 7.67/1.50  --instantiation_flag                    true
% 7.67/1.50  --inst_sos_flag                         true
% 7.67/1.50  --inst_sos_phase                        true
% 7.67/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.67/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.67/1.50  --inst_lit_sel_side                     num_symb
% 7.67/1.50  --inst_solver_per_active                1400
% 7.67/1.50  --inst_solver_calls_frac                1.
% 7.67/1.50  --inst_passive_queue_type               priority_queues
% 7.67/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.67/1.50  --inst_passive_queues_freq              [25;2]
% 7.67/1.50  --inst_dismatching                      true
% 7.67/1.50  --inst_eager_unprocessed_to_passive     true
% 7.67/1.50  --inst_prop_sim_given                   true
% 7.67/1.50  --inst_prop_sim_new                     false
% 7.67/1.50  --inst_subs_new                         false
% 7.67/1.50  --inst_eq_res_simp                      false
% 7.67/1.50  --inst_subs_given                       false
% 7.67/1.50  --inst_orphan_elimination               true
% 7.67/1.50  --inst_learning_loop_flag               true
% 7.67/1.50  --inst_learning_start                   3000
% 7.67/1.50  --inst_learning_factor                  2
% 7.67/1.50  --inst_start_prop_sim_after_learn       3
% 7.67/1.50  --inst_sel_renew                        solver
% 7.67/1.50  --inst_lit_activity_flag                true
% 7.67/1.50  --inst_restr_to_given                   false
% 7.67/1.50  --inst_activity_threshold               500
% 7.67/1.50  --inst_out_proof                        true
% 7.67/1.50  
% 7.67/1.50  ------ Resolution Options
% 7.67/1.50  
% 7.67/1.50  --resolution_flag                       true
% 7.67/1.50  --res_lit_sel                           adaptive
% 7.67/1.50  --res_lit_sel_side                      none
% 7.67/1.50  --res_ordering                          kbo
% 7.67/1.50  --res_to_prop_solver                    active
% 7.67/1.50  --res_prop_simpl_new                    false
% 7.67/1.50  --res_prop_simpl_given                  true
% 7.67/1.50  --res_passive_queue_type                priority_queues
% 7.67/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.67/1.50  --res_passive_queues_freq               [15;5]
% 7.67/1.50  --res_forward_subs                      full
% 7.67/1.50  --res_backward_subs                     full
% 7.67/1.50  --res_forward_subs_resolution           true
% 7.67/1.50  --res_backward_subs_resolution          true
% 7.67/1.50  --res_orphan_elimination                true
% 7.67/1.50  --res_time_limit                        2.
% 7.67/1.50  --res_out_proof                         true
% 7.67/1.50  
% 7.67/1.50  ------ Superposition Options
% 7.67/1.50  
% 7.67/1.50  --superposition_flag                    true
% 7.67/1.50  --sup_passive_queue_type                priority_queues
% 7.67/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.67/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.67/1.50  --demod_completeness_check              fast
% 7.67/1.50  --demod_use_ground                      true
% 7.67/1.50  --sup_to_prop_solver                    passive
% 7.67/1.50  --sup_prop_simpl_new                    true
% 7.67/1.50  --sup_prop_simpl_given                  true
% 7.67/1.50  --sup_fun_splitting                     true
% 7.67/1.50  --sup_smt_interval                      50000
% 7.67/1.50  
% 7.67/1.50  ------ Superposition Simplification Setup
% 7.67/1.50  
% 7.67/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.67/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.67/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.67/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.67/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.67/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.67/1.50  --sup_immed_triv                        [TrivRules]
% 7.67/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.50  --sup_immed_bw_main                     []
% 7.67/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.67/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.67/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.50  --sup_input_bw                          []
% 7.67/1.50  
% 7.67/1.50  ------ Combination Options
% 7.67/1.50  
% 7.67/1.50  --comb_res_mult                         3
% 7.67/1.50  --comb_sup_mult                         2
% 7.67/1.50  --comb_inst_mult                        10
% 7.67/1.50  
% 7.67/1.50  ------ Debug Options
% 7.67/1.50  
% 7.67/1.50  --dbg_backtrace                         false
% 7.67/1.50  --dbg_dump_prop_clauses                 false
% 7.67/1.50  --dbg_dump_prop_clauses_file            -
% 7.67/1.50  --dbg_out_stat                          false
% 7.67/1.50  ------ Parsing...
% 7.67/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.67/1.50  
% 7.67/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.67/1.50  
% 7.67/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.67/1.50  
% 7.67/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.50  ------ Proving...
% 7.67/1.50  ------ Problem Properties 
% 7.67/1.50  
% 7.67/1.50  
% 7.67/1.50  clauses                                 46
% 7.67/1.50  conjectures                             23
% 7.67/1.50  EPR                                     14
% 7.67/1.50  Horn                                    32
% 7.67/1.50  unary                                   14
% 7.67/1.50  binary                                  19
% 7.67/1.50  lits                                    151
% 7.67/1.50  lits eq                                 4
% 7.67/1.50  fd_pure                                 0
% 7.67/1.50  fd_pseudo                               0
% 7.67/1.50  fd_cond                                 0
% 7.67/1.50  fd_pseudo_cond                          0
% 7.67/1.50  AC symbols                              0
% 7.67/1.50  
% 7.67/1.50  ------ Schedule dynamic 5 is on 
% 7.67/1.50  
% 7.67/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.67/1.50  
% 7.67/1.50  
% 7.67/1.50  ------ 
% 7.67/1.50  Current options:
% 7.67/1.50  ------ 
% 7.67/1.50  
% 7.67/1.50  ------ Input Options
% 7.67/1.50  
% 7.67/1.50  --out_options                           all
% 7.67/1.50  --tptp_safe_out                         true
% 7.67/1.50  --problem_path                          ""
% 7.67/1.50  --include_path                          ""
% 7.67/1.50  --clausifier                            res/vclausify_rel
% 7.67/1.50  --clausifier_options                    ""
% 7.67/1.50  --stdin                                 false
% 7.67/1.50  --stats_out                             all
% 7.67/1.50  
% 7.67/1.50  ------ General Options
% 7.67/1.50  
% 7.67/1.50  --fof                                   false
% 7.67/1.50  --time_out_real                         305.
% 7.67/1.50  --time_out_virtual                      -1.
% 7.67/1.50  --symbol_type_check                     false
% 7.67/1.50  --clausify_out                          false
% 7.67/1.50  --sig_cnt_out                           false
% 7.67/1.50  --trig_cnt_out                          false
% 7.67/1.50  --trig_cnt_out_tolerance                1.
% 7.67/1.50  --trig_cnt_out_sk_spl                   false
% 7.67/1.50  --abstr_cl_out                          false
% 7.67/1.50  
% 7.67/1.50  ------ Global Options
% 7.67/1.50  
% 7.67/1.50  --schedule                              default
% 7.67/1.50  --add_important_lit                     false
% 7.67/1.50  --prop_solver_per_cl                    1000
% 7.67/1.50  --min_unsat_core                        false
% 7.67/1.50  --soft_assumptions                      false
% 7.67/1.50  --soft_lemma_size                       3
% 7.67/1.50  --prop_impl_unit_size                   0
% 7.67/1.50  --prop_impl_unit                        []
% 7.67/1.50  --share_sel_clauses                     true
% 7.67/1.50  --reset_solvers                         false
% 7.67/1.50  --bc_imp_inh                            [conj_cone]
% 7.67/1.50  --conj_cone_tolerance                   3.
% 7.67/1.50  --extra_neg_conj                        none
% 7.67/1.50  --large_theory_mode                     true
% 7.67/1.50  --prolific_symb_bound                   200
% 7.67/1.50  --lt_threshold                          2000
% 7.67/1.50  --clause_weak_htbl                      true
% 7.67/1.50  --gc_record_bc_elim                     false
% 7.67/1.50  
% 7.67/1.50  ------ Preprocessing Options
% 7.67/1.50  
% 7.67/1.50  --preprocessing_flag                    true
% 7.67/1.50  --time_out_prep_mult                    0.1
% 7.67/1.50  --splitting_mode                        input
% 7.67/1.50  --splitting_grd                         true
% 7.67/1.50  --splitting_cvd                         false
% 7.67/1.50  --splitting_cvd_svl                     false
% 7.67/1.50  --splitting_nvd                         32
% 7.67/1.50  --sub_typing                            true
% 7.67/1.50  --prep_gs_sim                           true
% 7.67/1.50  --prep_unflatten                        true
% 7.67/1.50  --prep_res_sim                          true
% 7.67/1.50  --prep_upred                            true
% 7.67/1.50  --prep_sem_filter                       exhaustive
% 7.67/1.50  --prep_sem_filter_out                   false
% 7.67/1.50  --pred_elim                             true
% 7.67/1.50  --res_sim_input                         true
% 7.67/1.50  --eq_ax_congr_red                       true
% 7.67/1.50  --pure_diseq_elim                       true
% 7.67/1.50  --brand_transform                       false
% 7.67/1.50  --non_eq_to_eq                          false
% 7.67/1.50  --prep_def_merge                        true
% 7.67/1.50  --prep_def_merge_prop_impl              false
% 7.67/1.50  --prep_def_merge_mbd                    true
% 7.67/1.50  --prep_def_merge_tr_red                 false
% 7.67/1.50  --prep_def_merge_tr_cl                  false
% 7.67/1.50  --smt_preprocessing                     true
% 7.67/1.50  --smt_ac_axioms                         fast
% 7.67/1.50  --preprocessed_out                      false
% 7.67/1.50  --preprocessed_stats                    false
% 7.67/1.50  
% 7.67/1.50  ------ Abstraction refinement Options
% 7.67/1.50  
% 7.67/1.50  --abstr_ref                             []
% 7.67/1.50  --abstr_ref_prep                        false
% 7.67/1.50  --abstr_ref_until_sat                   false
% 7.67/1.50  --abstr_ref_sig_restrict                funpre
% 7.67/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.67/1.50  --abstr_ref_under                       []
% 7.67/1.50  
% 7.67/1.50  ------ SAT Options
% 7.67/1.50  
% 7.67/1.50  --sat_mode                              false
% 7.67/1.50  --sat_fm_restart_options                ""
% 7.67/1.50  --sat_gr_def                            false
% 7.67/1.50  --sat_epr_types                         true
% 7.67/1.50  --sat_non_cyclic_types                  false
% 7.67/1.50  --sat_finite_models                     false
% 7.67/1.50  --sat_fm_lemmas                         false
% 7.67/1.50  --sat_fm_prep                           false
% 7.67/1.50  --sat_fm_uc_incr                        true
% 7.67/1.50  --sat_out_model                         small
% 7.67/1.50  --sat_out_clauses                       false
% 7.67/1.50  
% 7.67/1.50  ------ QBF Options
% 7.67/1.50  
% 7.67/1.50  --qbf_mode                              false
% 7.67/1.50  --qbf_elim_univ                         false
% 7.67/1.50  --qbf_dom_inst                          none
% 7.67/1.50  --qbf_dom_pre_inst                      false
% 7.67/1.50  --qbf_sk_in                             false
% 7.67/1.50  --qbf_pred_elim                         true
% 7.67/1.50  --qbf_split                             512
% 7.67/1.50  
% 7.67/1.50  ------ BMC1 Options
% 7.67/1.50  
% 7.67/1.50  --bmc1_incremental                      false
% 7.67/1.50  --bmc1_axioms                           reachable_all
% 7.67/1.50  --bmc1_min_bound                        0
% 7.67/1.50  --bmc1_max_bound                        -1
% 7.67/1.50  --bmc1_max_bound_default                -1
% 7.67/1.50  --bmc1_symbol_reachability              true
% 7.67/1.50  --bmc1_property_lemmas                  false
% 7.67/1.50  --bmc1_k_induction                      false
% 7.67/1.50  --bmc1_non_equiv_states                 false
% 7.67/1.50  --bmc1_deadlock                         false
% 7.67/1.50  --bmc1_ucm                              false
% 7.67/1.50  --bmc1_add_unsat_core                   none
% 7.67/1.50  --bmc1_unsat_core_children              false
% 7.67/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.67/1.50  --bmc1_out_stat                         full
% 7.67/1.50  --bmc1_ground_init                      false
% 7.67/1.50  --bmc1_pre_inst_next_state              false
% 7.67/1.50  --bmc1_pre_inst_state                   false
% 7.67/1.50  --bmc1_pre_inst_reach_state             false
% 7.67/1.50  --bmc1_out_unsat_core                   false
% 7.67/1.50  --bmc1_aig_witness_out                  false
% 7.67/1.50  --bmc1_verbose                          false
% 7.67/1.50  --bmc1_dump_clauses_tptp                false
% 7.67/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.67/1.50  --bmc1_dump_file                        -
% 7.67/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.67/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.67/1.50  --bmc1_ucm_extend_mode                  1
% 7.67/1.50  --bmc1_ucm_init_mode                    2
% 7.67/1.50  --bmc1_ucm_cone_mode                    none
% 7.67/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.67/1.50  --bmc1_ucm_relax_model                  4
% 7.67/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.67/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.67/1.50  --bmc1_ucm_layered_model                none
% 7.67/1.50  --bmc1_ucm_max_lemma_size               10
% 7.67/1.50  
% 7.67/1.50  ------ AIG Options
% 7.67/1.50  
% 7.67/1.50  --aig_mode                              false
% 7.67/1.50  
% 7.67/1.50  ------ Instantiation Options
% 7.67/1.50  
% 7.67/1.50  --instantiation_flag                    true
% 7.67/1.50  --inst_sos_flag                         true
% 7.67/1.50  --inst_sos_phase                        true
% 7.67/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.67/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.67/1.50  --inst_lit_sel_side                     none
% 7.67/1.50  --inst_solver_per_active                1400
% 7.67/1.50  --inst_solver_calls_frac                1.
% 7.67/1.50  --inst_passive_queue_type               priority_queues
% 7.67/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.67/1.50  --inst_passive_queues_freq              [25;2]
% 7.67/1.50  --inst_dismatching                      true
% 7.67/1.50  --inst_eager_unprocessed_to_passive     true
% 7.67/1.50  --inst_prop_sim_given                   true
% 7.67/1.50  --inst_prop_sim_new                     false
% 7.67/1.50  --inst_subs_new                         false
% 7.67/1.50  --inst_eq_res_simp                      false
% 7.67/1.50  --inst_subs_given                       false
% 7.67/1.50  --inst_orphan_elimination               true
% 7.67/1.50  --inst_learning_loop_flag               true
% 7.67/1.50  --inst_learning_start                   3000
% 7.67/1.50  --inst_learning_factor                  2
% 7.67/1.50  --inst_start_prop_sim_after_learn       3
% 7.67/1.50  --inst_sel_renew                        solver
% 7.67/1.50  --inst_lit_activity_flag                true
% 7.67/1.50  --inst_restr_to_given                   false
% 7.67/1.50  --inst_activity_threshold               500
% 7.67/1.50  --inst_out_proof                        true
% 7.67/1.50  
% 7.67/1.50  ------ Resolution Options
% 7.67/1.50  
% 7.67/1.50  --resolution_flag                       false
% 7.67/1.50  --res_lit_sel                           adaptive
% 7.67/1.50  --res_lit_sel_side                      none
% 7.67/1.50  --res_ordering                          kbo
% 7.67/1.50  --res_to_prop_solver                    active
% 7.67/1.50  --res_prop_simpl_new                    false
% 7.67/1.50  --res_prop_simpl_given                  true
% 7.67/1.50  --res_passive_queue_type                priority_queues
% 7.67/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.67/1.50  --res_passive_queues_freq               [15;5]
% 7.67/1.50  --res_forward_subs                      full
% 7.67/1.50  --res_backward_subs                     full
% 7.67/1.50  --res_forward_subs_resolution           true
% 7.67/1.50  --res_backward_subs_resolution          true
% 7.67/1.50  --res_orphan_elimination                true
% 7.67/1.50  --res_time_limit                        2.
% 7.67/1.50  --res_out_proof                         true
% 7.67/1.50  
% 7.67/1.50  ------ Superposition Options
% 7.67/1.50  
% 7.67/1.50  --superposition_flag                    true
% 7.67/1.50  --sup_passive_queue_type                priority_queues
% 7.67/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.67/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.67/1.50  --demod_completeness_check              fast
% 7.67/1.50  --demod_use_ground                      true
% 7.67/1.50  --sup_to_prop_solver                    passive
% 7.67/1.50  --sup_prop_simpl_new                    true
% 7.67/1.50  --sup_prop_simpl_given                  true
% 7.67/1.50  --sup_fun_splitting                     true
% 7.67/1.50  --sup_smt_interval                      50000
% 7.67/1.50  
% 7.67/1.50  ------ Superposition Simplification Setup
% 7.67/1.50  
% 7.67/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.67/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.67/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.67/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.67/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.67/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.67/1.50  --sup_immed_triv                        [TrivRules]
% 7.67/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.50  --sup_immed_bw_main                     []
% 7.67/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.67/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.67/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.50  --sup_input_bw                          []
% 7.67/1.50  
% 7.67/1.50  ------ Combination Options
% 7.67/1.50  
% 7.67/1.50  --comb_res_mult                         3
% 7.67/1.50  --comb_sup_mult                         2
% 7.67/1.50  --comb_inst_mult                        10
% 7.67/1.50  
% 7.67/1.50  ------ Debug Options
% 7.67/1.50  
% 7.67/1.50  --dbg_backtrace                         false
% 7.67/1.50  --dbg_dump_prop_clauses                 false
% 7.67/1.50  --dbg_dump_prop_clauses_file            -
% 7.67/1.50  --dbg_out_stat                          false
% 7.67/1.50  
% 7.67/1.50  
% 7.67/1.50  
% 7.67/1.50  
% 7.67/1.50  ------ Proving...
% 7.67/1.50  
% 7.67/1.50  
% 7.67/1.50  % SZS status Theorem for theBenchmark.p
% 7.67/1.50  
% 7.67/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.67/1.50  
% 7.67/1.50  fof(f8,axiom,(
% 7.67/1.50    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 7.67/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f24,plain,(
% 7.67/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 7.67/1.50    inference(ennf_transformation,[],[f8])).
% 7.67/1.50  
% 7.67/1.50  fof(f25,plain,(
% 7.67/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 7.67/1.50    inference(flattening,[],[f24])).
% 7.67/1.50  
% 7.67/1.50  fof(f57,plain,(
% 7.67/1.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f25])).
% 7.67/1.50  
% 7.67/1.50  fof(f11,conjecture,(
% 7.67/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 7.67/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f12,negated_conjecture,(
% 7.67/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 7.67/1.50    inference(negated_conjecture,[],[f11])).
% 7.67/1.50  
% 7.67/1.50  fof(f29,plain,(
% 7.67/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & (r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0)) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.67/1.50    inference(ennf_transformation,[],[f12])).
% 7.67/1.50  
% 7.67/1.50  fof(f30,plain,(
% 7.67/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.67/1.50    inference(flattening,[],[f29])).
% 7.67/1.50  
% 7.67/1.50  fof(f40,plain,(
% 7.67/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.67/1.50    inference(nnf_transformation,[],[f30])).
% 7.67/1.50  
% 7.67/1.50  fof(f41,plain,(
% 7.67/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.67/1.50    inference(flattening,[],[f40])).
% 7.67/1.50  
% 7.67/1.50  fof(f46,plain,(
% 7.67/1.50    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((~m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,sK6) & k1_tsep_1(X0,X3,sK6) = X0 & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 7.67/1.50    introduced(choice_axiom,[])).
% 7.67/1.50  
% 7.67/1.50  fof(f45,plain,(
% 7.67/1.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK5)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK5))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,sK5,X4) & k1_tsep_1(X0,sK5,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 7.67/1.50    introduced(choice_axiom,[])).
% 7.67/1.50  
% 7.67/1.50  fof(f44,plain,(
% 7.67/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(sK4,X0,X1) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) & m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X3))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK4,X0,X1) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 7.67/1.50    introduced(choice_axiom,[])).
% 7.67/1.50  
% 7.67/1.50  fof(f43,plain,(
% 7.67/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(X2,X0,sK3) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) & m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v5_pre_topc(X2,X0,sK3) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 7.67/1.50    introduced(choice_axiom,[])).
% 7.67/1.50  
% 7.67/1.50  fof(f42,plain,(
% 7.67/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(sK2,X3,X4) & k1_tsep_1(sK2,X3,X4) = sK2 & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 7.67/1.50    introduced(choice_axiom,[])).
% 7.67/1.50  
% 7.67/1.50  fof(f47,plain,(
% 7.67/1.50    (((((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,sK5,sK6) & k1_tsep_1(sK2,sK5,sK6) = sK2 & m1_pre_topc(sK6,sK2) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 7.67/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f41,f46,f45,f44,f43,f42])).
% 7.67/1.50  
% 7.67/1.50  fof(f121,plain,(
% 7.67/1.50    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 7.67/1.50    inference(cnf_transformation,[],[f47])).
% 7.67/1.50  
% 7.67/1.50  fof(f80,plain,(
% 7.67/1.50    v1_funct_1(sK4)),
% 7.67/1.50    inference(cnf_transformation,[],[f47])).
% 7.67/1.50  
% 7.67/1.50  fof(f81,plain,(
% 7.67/1.50    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 7.67/1.50    inference(cnf_transformation,[],[f47])).
% 7.67/1.50  
% 7.67/1.50  fof(f82,plain,(
% 7.67/1.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 7.67/1.50    inference(cnf_transformation,[],[f47])).
% 7.67/1.50  
% 7.67/1.50  fof(f76,plain,(
% 7.67/1.50    l1_pre_topc(sK2)),
% 7.67/1.50    inference(cnf_transformation,[],[f47])).
% 7.67/1.50  
% 7.67/1.50  fof(f79,plain,(
% 7.67/1.50    l1_pre_topc(sK3)),
% 7.67/1.50    inference(cnf_transformation,[],[f47])).
% 7.67/1.50  
% 7.67/1.50  fof(f5,axiom,(
% 7.67/1.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.67/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f20,plain,(
% 7.67/1.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.67/1.50    inference(ennf_transformation,[],[f5])).
% 7.67/1.50  
% 7.67/1.50  fof(f52,plain,(
% 7.67/1.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f20])).
% 7.67/1.50  
% 7.67/1.50  fof(f6,axiom,(
% 7.67/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.67/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f21,plain,(
% 7.67/1.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.67/1.50    inference(ennf_transformation,[],[f6])).
% 7.67/1.50  
% 7.67/1.50  fof(f53,plain,(
% 7.67/1.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f21])).
% 7.67/1.50  
% 7.67/1.50  fof(f84,plain,(
% 7.67/1.50    m1_pre_topc(sK5,sK2)),
% 7.67/1.50    inference(cnf_transformation,[],[f47])).
% 7.67/1.50  
% 7.67/1.50  fof(f55,plain,(
% 7.67/1.50    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f25])).
% 7.67/1.50  
% 7.67/1.50  fof(f86,plain,(
% 7.67/1.50    m1_pre_topc(sK6,sK2)),
% 7.67/1.50    inference(cnf_transformation,[],[f47])).
% 7.67/1.50  
% 7.67/1.50  fof(f56,plain,(
% 7.67/1.50    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f25])).
% 7.67/1.50  
% 7.67/1.50  fof(f77,plain,(
% 7.67/1.50    ~v2_struct_0(sK3)),
% 7.67/1.50    inference(cnf_transformation,[],[f47])).
% 7.67/1.50  
% 7.67/1.50  fof(f78,plain,(
% 7.67/1.50    v2_pre_topc(sK3)),
% 7.67/1.50    inference(cnf_transformation,[],[f47])).
% 7.67/1.50  
% 7.67/1.50  fof(f32,plain,(
% 7.67/1.50    ! [X2,X0,X4,X3,X1] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> sP0(X1,X3,X4,X0,X2)) | ~sP1(X2,X0,X4,X3,X1))),
% 7.67/1.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 7.67/1.50  
% 7.67/1.50  fof(f34,plain,(
% 7.67/1.50    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))))) | ~sP1(X2,X0,X4,X3,X1))),
% 7.67/1.50    inference(nnf_transformation,[],[f32])).
% 7.67/1.50  
% 7.67/1.50  fof(f35,plain,(
% 7.67/1.50    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))))) | ~sP1(X2,X0,X4,X3,X1))),
% 7.67/1.50    inference(flattening,[],[f34])).
% 7.67/1.50  
% 7.67/1.50  fof(f36,plain,(
% 7.67/1.50    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) & v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) & v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) & v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))))) | ~sP1(X0,X1,X2,X3,X4))),
% 7.67/1.50    inference(rectify,[],[f35])).
% 7.67/1.50  
% 7.67/1.50  fof(f58,plain,(
% 7.67/1.50    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f36])).
% 7.67/1.50  
% 7.67/1.50  fof(f9,axiom,(
% 7.67/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))))))))),
% 7.67/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f26,plain,(
% 7.67/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.67/1.50    inference(ennf_transformation,[],[f9])).
% 7.67/1.50  
% 7.67/1.50  fof(f27,plain,(
% 7.67/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.50    inference(flattening,[],[f26])).
% 7.67/1.50  
% 7.67/1.50  fof(f31,plain,(
% 7.67/1.50    ! [X1,X3,X4,X0,X2] : (sP0(X1,X3,X4,X0,X2) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))),
% 7.67/1.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.67/1.50  
% 7.67/1.50  fof(f33,plain,(
% 7.67/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X2,X0,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.50    inference(definition_folding,[],[f27,f32,f31])).
% 7.67/1.50  
% 7.67/1.50  fof(f72,plain,(
% 7.67/1.50    ( ! [X4,X2,X0,X3,X1] : (sP1(X2,X0,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f33])).
% 7.67/1.50  
% 7.67/1.50  fof(f88,plain,(
% 7.67/1.50    r4_tsep_1(sK2,sK5,sK6)),
% 7.67/1.50    inference(cnf_transformation,[],[f47])).
% 7.67/1.50  
% 7.67/1.50  fof(f74,plain,(
% 7.67/1.50    ~v2_struct_0(sK2)),
% 7.67/1.50    inference(cnf_transformation,[],[f47])).
% 7.67/1.50  
% 7.67/1.50  fof(f75,plain,(
% 7.67/1.50    v2_pre_topc(sK2)),
% 7.67/1.50    inference(cnf_transformation,[],[f47])).
% 7.67/1.50  
% 7.67/1.50  fof(f83,plain,(
% 7.67/1.50    ~v2_struct_0(sK5)),
% 7.67/1.50    inference(cnf_transformation,[],[f47])).
% 7.67/1.50  
% 7.67/1.50  fof(f85,plain,(
% 7.67/1.50    ~v2_struct_0(sK6)),
% 7.67/1.50    inference(cnf_transformation,[],[f47])).
% 7.67/1.50  
% 7.67/1.50  fof(f87,plain,(
% 7.67/1.50    k1_tsep_1(sK2,sK5,sK6) = sK2),
% 7.67/1.50    inference(cnf_transformation,[],[f47])).
% 7.67/1.50  
% 7.67/1.50  fof(f3,axiom,(
% 7.67/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.67/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f13,plain,(
% 7.67/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.67/1.50    inference(pure_predicate_removal,[],[f3])).
% 7.67/1.50  
% 7.67/1.50  fof(f17,plain,(
% 7.67/1.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.50    inference(ennf_transformation,[],[f13])).
% 7.67/1.50  
% 7.67/1.50  fof(f50,plain,(
% 7.67/1.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.50    inference(cnf_transformation,[],[f17])).
% 7.67/1.50  
% 7.67/1.50  fof(f1,axiom,(
% 7.67/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.67/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f14,plain,(
% 7.67/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.67/1.50    inference(ennf_transformation,[],[f1])).
% 7.67/1.50  
% 7.67/1.50  fof(f15,plain,(
% 7.67/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.67/1.50    inference(flattening,[],[f14])).
% 7.67/1.50  
% 7.67/1.50  fof(f48,plain,(
% 7.67/1.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f15])).
% 7.67/1.50  
% 7.67/1.50  fof(f2,axiom,(
% 7.67/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.67/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f16,plain,(
% 7.67/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.50    inference(ennf_transformation,[],[f2])).
% 7.67/1.50  
% 7.67/1.50  fof(f49,plain,(
% 7.67/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.50    inference(cnf_transformation,[],[f16])).
% 7.67/1.50  
% 7.67/1.50  fof(f10,axiom,(
% 7.67/1.50    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.67/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f28,plain,(
% 7.67/1.50    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.67/1.50    inference(ennf_transformation,[],[f10])).
% 7.67/1.50  
% 7.67/1.50  fof(f73,plain,(
% 7.67/1.50    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f28])).
% 7.67/1.50  
% 7.67/1.50  fof(f7,axiom,(
% 7.67/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 7.67/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f22,plain,(
% 7.67/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.67/1.50    inference(ennf_transformation,[],[f7])).
% 7.67/1.50  
% 7.67/1.50  fof(f23,plain,(
% 7.67/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.50    inference(flattening,[],[f22])).
% 7.67/1.50  
% 7.67/1.50  fof(f54,plain,(
% 7.67/1.50    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f23])).
% 7.67/1.50  
% 7.67/1.50  fof(f4,axiom,(
% 7.67/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.67/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f18,plain,(
% 7.67/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.67/1.50    inference(ennf_transformation,[],[f4])).
% 7.67/1.50  
% 7.67/1.50  fof(f19,plain,(
% 7.67/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.67/1.50    inference(flattening,[],[f18])).
% 7.67/1.50  
% 7.67/1.50  fof(f51,plain,(
% 7.67/1.50    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f19])).
% 7.67/1.50  
% 7.67/1.50  fof(f37,plain,(
% 7.67/1.50    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 7.67/1.50    inference(nnf_transformation,[],[f31])).
% 7.67/1.50  
% 7.67/1.50  fof(f38,plain,(
% 7.67/1.50    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 7.67/1.50    inference(flattening,[],[f37])).
% 7.67/1.50  
% 7.67/1.50  fof(f39,plain,(
% 7.67/1.50    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) & ((m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 7.67/1.50    inference(rectify,[],[f38])).
% 7.67/1.50  
% 7.67/1.50  fof(f65,plain,(
% 7.67/1.50    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f39])).
% 7.67/1.50  
% 7.67/1.50  fof(f69,plain,(
% 7.67/1.50    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f39])).
% 7.67/1.50  
% 7.67/1.50  fof(f99,plain,(
% 7.67/1.50    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 7.67/1.50    inference(cnf_transformation,[],[f47])).
% 7.67/1.50  
% 7.67/1.50  fof(f115,plain,(
% 7.67/1.50    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 7.67/1.50    inference(cnf_transformation,[],[f47])).
% 7.67/1.50  
% 7.67/1.50  fof(f119,plain,(
% 7.67/1.50    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 7.67/1.50    inference(cnf_transformation,[],[f47])).
% 7.67/1.50  
% 7.67/1.50  fof(f71,plain,(
% 7.67/1.50    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) )),
% 7.67/1.50    inference(cnf_transformation,[],[f39])).
% 7.67/1.50  
% 7.67/1.50  fof(f62,plain,(
% 7.67/1.50    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f36])).
% 7.67/1.50  
% 7.67/1.50  fof(f61,plain,(
% 7.67/1.50    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f36])).
% 7.67/1.50  
% 7.67/1.50  fof(f60,plain,(
% 7.67/1.50    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f36])).
% 7.67/1.50  
% 7.67/1.50  fof(f59,plain,(
% 7.67/1.50    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f36])).
% 7.67/1.50  
% 7.67/1.50  cnf(c_7,plain,
% 7.67/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.67/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.67/1.50      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 7.67/1.50      | ~ l1_struct_0(X3)
% 7.67/1.50      | ~ l1_struct_0(X2)
% 7.67/1.50      | ~ l1_struct_0(X1)
% 7.67/1.50      | ~ v1_funct_1(X0) ),
% 7.67/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_2673,plain,
% 7.67/1.50      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.67/1.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.67/1.50      | m1_subset_1(k2_tmap_1(X0_54,X1_54,X0_55,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 7.67/1.50      | ~ l1_struct_0(X2_54)
% 7.67/1.50      | ~ l1_struct_0(X1_54)
% 7.67/1.50      | ~ l1_struct_0(X0_54)
% 7.67/1.50      | ~ v1_funct_1(X0_55) ),
% 7.67/1.50      inference(subtyping,[status(esa)],[c_7]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_3516,plain,
% 7.67/1.50      ( v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.67/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.67/1.50      | m1_subset_1(k2_tmap_1(X0_54,X1_54,X0_55,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) = iProver_top
% 7.67/1.50      | l1_struct_0(X2_54) != iProver_top
% 7.67/1.50      | l1_struct_0(X1_54) != iProver_top
% 7.67/1.50      | l1_struct_0(X0_54) != iProver_top
% 7.67/1.50      | v1_funct_1(X0_55) != iProver_top ),
% 7.67/1.50      inference(predicate_to_equality,[status(thm)],[c_2673]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_26,negated_conjecture,
% 7.67/1.50      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.67/1.50      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.67/1.50      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.67/1.50      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.67/1.50      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.67/1.50      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.67/1.50      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.67/1.50      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.67/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.67/1.50      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.67/1.50      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 7.67/1.50      | ~ v1_funct_1(sK4) ),
% 7.67/1.50      inference(cnf_transformation,[],[f121]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_67,negated_conjecture,
% 7.67/1.50      ( v1_funct_1(sK4) ),
% 7.67/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_66,negated_conjecture,
% 7.67/1.50      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 7.67/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_65,negated_conjecture,
% 7.67/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 7.67/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_478,plain,
% 7.67/1.50      ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 7.67/1.50      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.67/1.50      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.67/1.50      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.67/1.50      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.67/1.50      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.67/1.50      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.67/1.50      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.67/1.50      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 7.67/1.50      inference(global_propositional_subsumption,
% 7.67/1.50                [status(thm)],
% 7.67/1.50                [c_26,c_67,c_66,c_65]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_479,negated_conjecture,
% 7.67/1.50      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.67/1.50      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.67/1.50      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.67/1.50      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.67/1.50      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.67/1.50      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.67/1.50      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.67/1.50      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.67/1.50      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 7.67/1.50      inference(renaming,[status(thm)],[c_478]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_2638,negated_conjecture,
% 7.67/1.50      ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.67/1.50      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.67/1.50      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.67/1.50      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.67/1.50      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 7.67/1.50      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.67/1.50      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 7.67/1.50      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.67/1.50      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 7.67/1.50      inference(subtyping,[status(esa)],[c_479]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_3550,plain,
% 7.67/1.50      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.67/1.50      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.67/1.50      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.67/1.50      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.67/1.50      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.67/1.50      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.67/1.50      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.67/1.50      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 7.67/1.50      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 7.67/1.50      inference(predicate_to_equality,[status(thm)],[c_2638]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_71,negated_conjecture,
% 7.67/1.50      ( l1_pre_topc(sK2) ),
% 7.67/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_76,plain,
% 7.67/1.50      ( l1_pre_topc(sK2) = iProver_top ),
% 7.67/1.50      inference(predicate_to_equality,[status(thm)],[c_71]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_68,negated_conjecture,
% 7.67/1.50      ( l1_pre_topc(sK3) ),
% 7.67/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_79,plain,
% 7.67/1.50      ( l1_pre_topc(sK3) = iProver_top ),
% 7.67/1.50      inference(predicate_to_equality,[status(thm)],[c_68]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_80,plain,
% 7.67/1.50      ( v1_funct_1(sK4) = iProver_top ),
% 7.67/1.50      inference(predicate_to_equality,[status(thm)],[c_67]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_81,plain,
% 7.67/1.50      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 7.67/1.50      inference(predicate_to_equality,[status(thm)],[c_66]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_82,plain,
% 7.67/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 7.67/1.50      inference(predicate_to_equality,[status(thm)],[c_65]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_4,plain,
% 7.67/1.50      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.67/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_174,plain,
% 7.67/1.50      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 7.67/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_176,plain,
% 7.67/1.50      ( l1_pre_topc(sK3) != iProver_top
% 7.67/1.50      | l1_struct_0(sK3) = iProver_top ),
% 7.67/1.50      inference(instantiation,[status(thm)],[c_174]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_480,plain,
% 7.67/1.50      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.67/1.50      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.67/1.50      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.67/1.50      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.67/1.50      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.67/1.50      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.67/1.50      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.67/1.50      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 7.67/1.50      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 7.67/1.50      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_5,plain,
% 7.67/1.50      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.67/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_63,negated_conjecture,
% 7.67/1.50      ( m1_pre_topc(sK5,sK2) ),
% 7.67/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_816,plain,
% 7.67/1.50      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK5 != X1 | sK2 != X0 ),
% 7.67/1.50      inference(resolution_lifted,[status(thm)],[c_5,c_63]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_817,plain,
% 7.67/1.50      ( l1_pre_topc(sK5) | ~ l1_pre_topc(sK2) ),
% 7.67/1.50      inference(unflattening,[status(thm)],[c_816]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_818,plain,
% 7.67/1.50      ( l1_pre_topc(sK5) = iProver_top
% 7.67/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.67/1.50      inference(predicate_to_equality,[status(thm)],[c_817]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_9,plain,
% 7.67/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.67/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.67/1.50      | ~ l1_struct_0(X3)
% 7.67/1.50      | ~ l1_struct_0(X2)
% 7.67/1.50      | ~ l1_struct_0(X1)
% 7.67/1.50      | ~ v1_funct_1(X0)
% 7.67/1.50      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 7.67/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_2671,plain,
% 7.67/1.50      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.67/1.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.67/1.50      | ~ l1_struct_0(X2_54)
% 7.67/1.50      | ~ l1_struct_0(X1_54)
% 7.67/1.50      | ~ l1_struct_0(X0_54)
% 7.67/1.50      | ~ v1_funct_1(X0_55)
% 7.67/1.50      | v1_funct_1(k2_tmap_1(X0_54,X1_54,X0_55,X2_54)) ),
% 7.67/1.50      inference(subtyping,[status(esa)],[c_9]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_3659,plain,
% 7.67/1.50      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.67/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.67/1.50      | ~ l1_struct_0(sK5)
% 7.67/1.50      | ~ l1_struct_0(sK3)
% 7.67/1.50      | ~ l1_struct_0(sK2)
% 7.67/1.50      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 7.67/1.50      | ~ v1_funct_1(sK4) ),
% 7.67/1.50      inference(instantiation,[status(thm)],[c_2671]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_3660,plain,
% 7.67/1.50      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.67/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.67/1.50      | l1_struct_0(sK5) != iProver_top
% 7.67/1.50      | l1_struct_0(sK3) != iProver_top
% 7.67/1.50      | l1_struct_0(sK2) != iProver_top
% 7.67/1.50      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top
% 7.67/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.67/1.50      inference(predicate_to_equality,[status(thm)],[c_3659]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_2676,plain,
% 7.67/1.50      ( ~ l1_pre_topc(X0_54) | l1_struct_0(X0_54) ),
% 7.67/1.50      inference(subtyping,[status(esa)],[c_4]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_3731,plain,
% 7.67/1.50      ( ~ l1_pre_topc(sK5) | l1_struct_0(sK5) ),
% 7.67/1.50      inference(instantiation,[status(thm)],[c_2676]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_3732,plain,
% 7.67/1.50      ( l1_pre_topc(sK5) != iProver_top
% 7.67/1.50      | l1_struct_0(sK5) = iProver_top ),
% 7.67/1.50      inference(predicate_to_equality,[status(thm)],[c_3731]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_3823,plain,
% 7.67/1.50      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 7.67/1.50      inference(instantiation,[status(thm)],[c_2676]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_3824,plain,
% 7.67/1.50      ( l1_pre_topc(sK2) != iProver_top
% 7.67/1.50      | l1_struct_0(sK2) = iProver_top ),
% 7.67/1.50      inference(predicate_to_equality,[status(thm)],[c_3823]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_3978,plain,
% 7.67/1.50      ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.67/1.50      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.67/1.50      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.67/1.50      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.67/1.50      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.67/1.50      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.67/1.50      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.67/1.50      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 7.67/1.50      inference(global_propositional_subsumption,
% 7.67/1.50                [status(thm)],
% 7.67/1.50                [c_3550,c_76,c_79,c_80,c_81,c_82,c_176,c_480,c_818,
% 7.67/1.50                 c_3660,c_3732,c_3824]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_3979,plain,
% 7.67/1.50      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.67/1.50      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.67/1.50      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.67/1.50      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.67/1.50      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.67/1.50      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.67/1.50      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.67/1.50      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 7.67/1.50      inference(renaming,[status(thm)],[c_3978]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_5188,plain,
% 7.67/1.50      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.67/1.50      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.67/1.50      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.67/1.50      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.67/1.50      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.67/1.50      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.67/1.50      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.67/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.67/1.50      | l1_struct_0(sK5) != iProver_top
% 7.67/1.50      | l1_struct_0(sK3) != iProver_top
% 7.67/1.50      | l1_struct_0(sK2) != iProver_top
% 7.67/1.50      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top
% 7.67/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_3516,c_3979]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_61,negated_conjecture,
% 7.67/1.50      ( m1_pre_topc(sK6,sK2) ),
% 7.67/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_805,plain,
% 7.67/1.50      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK6 != X1 | sK2 != X0 ),
% 7.67/1.50      inference(resolution_lifted,[status(thm)],[c_5,c_61]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_806,plain,
% 7.67/1.50      ( l1_pre_topc(sK6) | ~ l1_pre_topc(sK2) ),
% 7.67/1.50      inference(unflattening,[status(thm)],[c_805]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_807,plain,
% 7.67/1.50      ( l1_pre_topc(sK6) = iProver_top
% 7.67/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.67/1.50      inference(predicate_to_equality,[status(thm)],[c_806]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_4035,plain,
% 7.67/1.50      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.67/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.67/1.50      | ~ l1_struct_0(X0_54)
% 7.67/1.50      | ~ l1_struct_0(sK3)
% 7.67/1.50      | ~ l1_struct_0(sK2)
% 7.67/1.50      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_54))
% 7.67/1.50      | ~ v1_funct_1(sK4) ),
% 7.67/1.50      inference(instantiation,[status(thm)],[c_2671]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_4054,plain,
% 7.67/1.50      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.67/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.67/1.50      | ~ l1_struct_0(sK6)
% 7.67/1.50      | ~ l1_struct_0(sK3)
% 7.67/1.50      | ~ l1_struct_0(sK2)
% 7.67/1.50      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 7.67/1.50      | ~ v1_funct_1(sK4) ),
% 7.67/1.50      inference(instantiation,[status(thm)],[c_4035]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_4055,plain,
% 7.67/1.50      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.67/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.67/1.50      | l1_struct_0(sK6) != iProver_top
% 7.67/1.50      | l1_struct_0(sK3) != iProver_top
% 7.67/1.50      | l1_struct_0(sK2) != iProver_top
% 7.67/1.50      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top
% 7.67/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.67/1.50      inference(predicate_to_equality,[status(thm)],[c_4054]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_4099,plain,
% 7.67/1.50      ( ~ l1_pre_topc(sK6) | l1_struct_0(sK6) ),
% 7.67/1.50      inference(instantiation,[status(thm)],[c_2676]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_4100,plain,
% 7.67/1.50      ( l1_pre_topc(sK6) != iProver_top
% 7.67/1.50      | l1_struct_0(sK6) = iProver_top ),
% 7.67/1.50      inference(predicate_to_equality,[status(thm)],[c_4099]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_8,plain,
% 7.67/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.67/1.50      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 7.67/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.67/1.50      | ~ l1_struct_0(X3)
% 7.67/1.50      | ~ l1_struct_0(X2)
% 7.67/1.50      | ~ l1_struct_0(X1)
% 7.67/1.50      | ~ v1_funct_1(X0) ),
% 7.67/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_2672,plain,
% 7.67/1.50      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.67/1.50      | v1_funct_2(k2_tmap_1(X0_54,X1_54,X0_55,X2_54),u1_struct_0(X2_54),u1_struct_0(X1_54))
% 7.67/1.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.67/1.50      | ~ l1_struct_0(X2_54)
% 7.67/1.50      | ~ l1_struct_0(X1_54)
% 7.67/1.50      | ~ l1_struct_0(X0_54)
% 7.67/1.50      | ~ v1_funct_1(X0_55) ),
% 7.67/1.50      inference(subtyping,[status(esa)],[c_8]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_4144,plain,
% 7.67/1.50      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_54),u1_struct_0(X0_54),u1_struct_0(sK3))
% 7.67/1.50      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.67/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.67/1.50      | ~ l1_struct_0(X0_54)
% 7.67/1.50      | ~ l1_struct_0(sK3)
% 7.67/1.50      | ~ l1_struct_0(sK2)
% 7.67/1.50      | ~ v1_funct_1(sK4) ),
% 7.67/1.50      inference(instantiation,[status(thm)],[c_2672]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_4509,plain,
% 7.67/1.50      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.67/1.50      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.67/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.67/1.51      | ~ l1_struct_0(sK5)
% 7.67/1.51      | ~ l1_struct_0(sK3)
% 7.67/1.51      | ~ l1_struct_0(sK2)
% 7.67/1.51      | ~ v1_funct_1(sK4) ),
% 7.67/1.51      inference(instantiation,[status(thm)],[c_4144]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_4510,plain,
% 7.67/1.51      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
% 7.67/1.51      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.67/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.67/1.51      | l1_struct_0(sK5) != iProver_top
% 7.67/1.51      | l1_struct_0(sK3) != iProver_top
% 7.67/1.51      | l1_struct_0(sK2) != iProver_top
% 7.67/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_4509]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_4457,plain,
% 7.67/1.51      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.67/1.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
% 7.67/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.67/1.51      | ~ l1_struct_0(X0_54)
% 7.67/1.51      | ~ l1_struct_0(sK3)
% 7.67/1.51      | ~ l1_struct_0(sK2)
% 7.67/1.51      | ~ v1_funct_1(sK4) ),
% 7.67/1.51      inference(instantiation,[status(thm)],[c_2673]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_4955,plain,
% 7.67/1.51      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.67/1.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.67/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.67/1.51      | ~ l1_struct_0(sK5)
% 7.67/1.51      | ~ l1_struct_0(sK3)
% 7.67/1.51      | ~ l1_struct_0(sK2)
% 7.67/1.51      | ~ v1_funct_1(sK4) ),
% 7.67/1.51      inference(instantiation,[status(thm)],[c_4457]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_4956,plain,
% 7.67/1.51      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.67/1.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top
% 7.67/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.67/1.51      | l1_struct_0(sK5) != iProver_top
% 7.67/1.51      | l1_struct_0(sK3) != iProver_top
% 7.67/1.51      | l1_struct_0(sK2) != iProver_top
% 7.67/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_4955]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_5611,plain,
% 7.67/1.51      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.67/1.51      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.67/1.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top ),
% 7.67/1.51      inference(global_propositional_subsumption,
% 7.67/1.51                [status(thm)],
% 7.67/1.51                [c_5188,c_76,c_79,c_80,c_81,c_82,c_176,c_480,c_807,c_818,
% 7.67/1.51                 c_3660,c_3732,c_3824,c_4055,c_4100,c_4510,c_4956]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_5612,plain,
% 7.67/1.51      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.67/1.51      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.67/1.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.67/1.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top ),
% 7.67/1.51      inference(renaming,[status(thm)],[c_5611]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_5616,plain,
% 7.67/1.51      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.67/1.51      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.67/1.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.67/1.51      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.67/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.67/1.51      | l1_struct_0(sK6) != iProver_top
% 7.67/1.51      | l1_struct_0(sK3) != iProver_top
% 7.67/1.51      | l1_struct_0(sK2) != iProver_top
% 7.67/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.67/1.51      inference(superposition,[status(thm)],[c_3516,c_5612]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_70,negated_conjecture,
% 7.67/1.51      ( ~ v2_struct_0(sK3) ),
% 7.67/1.51      inference(cnf_transformation,[],[f77]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_77,plain,
% 7.67/1.51      ( v2_struct_0(sK3) != iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_70]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_69,negated_conjecture,
% 7.67/1.51      ( v2_pre_topc(sK3) ),
% 7.67/1.51      inference(cnf_transformation,[],[f78]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_78,plain,
% 7.67/1.51      ( v2_pre_topc(sK3) = iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_69]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_2647,negated_conjecture,
% 7.67/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 7.67/1.51      inference(subtyping,[status(esa)],[c_65]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3541,plain,
% 7.67/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_2647]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3517,plain,
% 7.67/1.51      ( v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.67/1.51      | v1_funct_2(k2_tmap_1(X0_54,X1_54,X0_55,X2_54),u1_struct_0(X2_54),u1_struct_0(X1_54)) = iProver_top
% 7.67/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.67/1.51      | l1_struct_0(X2_54) != iProver_top
% 7.67/1.51      | l1_struct_0(X1_54) != iProver_top
% 7.67/1.51      | l1_struct_0(X0_54) != iProver_top
% 7.67/1.51      | v1_funct_1(X0_55) != iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_2672]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_14,plain,
% 7.67/1.51      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.67/1.51      | sP0(X4,X3,X2,X1,X0)
% 7.67/1.51      | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
% 7.67/1.51      | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
% 7.67/1.51      | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
% 7.67/1.51      | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
% 7.67/1.51      inference(cnf_transformation,[],[f58]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_24,plain,
% 7.67/1.51      ( sP1(X0,X1,X2,X3,X4)
% 7.67/1.51      | ~ r4_tsep_1(X1,X0,X3)
% 7.67/1.51      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
% 7.67/1.51      | ~ m1_pre_topc(X3,X1)
% 7.67/1.51      | ~ m1_pre_topc(X0,X1)
% 7.67/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 7.67/1.51      | v2_struct_0(X1)
% 7.67/1.51      | v2_struct_0(X4)
% 7.67/1.51      | v2_struct_0(X0)
% 7.67/1.51      | v2_struct_0(X3)
% 7.67/1.51      | ~ v2_pre_topc(X4)
% 7.67/1.51      | ~ v2_pre_topc(X1)
% 7.67/1.51      | ~ l1_pre_topc(X1)
% 7.67/1.51      | ~ l1_pre_topc(X4)
% 7.67/1.51      | ~ v1_funct_1(X2) ),
% 7.67/1.51      inference(cnf_transformation,[],[f72]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_59,negated_conjecture,
% 7.67/1.51      ( r4_tsep_1(sK2,sK5,sK6) ),
% 7.67/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_762,plain,
% 7.67/1.51      ( sP1(X0,X1,X2,X3,X4)
% 7.67/1.51      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
% 7.67/1.51      | ~ m1_pre_topc(X0,X1)
% 7.67/1.51      | ~ m1_pre_topc(X3,X1)
% 7.67/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 7.67/1.51      | v2_struct_0(X1)
% 7.67/1.51      | v2_struct_0(X0)
% 7.67/1.51      | v2_struct_0(X3)
% 7.67/1.51      | v2_struct_0(X4)
% 7.67/1.51      | ~ v2_pre_topc(X1)
% 7.67/1.51      | ~ v2_pre_topc(X4)
% 7.67/1.51      | ~ l1_pre_topc(X1)
% 7.67/1.51      | ~ l1_pre_topc(X4)
% 7.67/1.51      | ~ v1_funct_1(X2)
% 7.67/1.51      | sK5 != X0
% 7.67/1.51      | sK6 != X3
% 7.67/1.51      | sK2 != X1 ),
% 7.67/1.51      inference(resolution_lifted,[status(thm)],[c_24,c_59]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_763,plain,
% 7.67/1.51      ( sP1(sK5,sK2,X0,sK6,X1)
% 7.67/1.51      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 7.67/1.51      | ~ m1_pre_topc(sK5,sK2)
% 7.67/1.51      | ~ m1_pre_topc(sK6,sK2)
% 7.67/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 7.67/1.51      | v2_struct_0(X1)
% 7.67/1.51      | v2_struct_0(sK5)
% 7.67/1.51      | v2_struct_0(sK6)
% 7.67/1.51      | v2_struct_0(sK2)
% 7.67/1.51      | ~ v2_pre_topc(X1)
% 7.67/1.51      | ~ v2_pre_topc(sK2)
% 7.67/1.51      | ~ l1_pre_topc(X1)
% 7.67/1.51      | ~ l1_pre_topc(sK2)
% 7.67/1.51      | ~ v1_funct_1(X0) ),
% 7.67/1.51      inference(unflattening,[status(thm)],[c_762]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_73,negated_conjecture,
% 7.67/1.51      ( ~ v2_struct_0(sK2) ),
% 7.67/1.51      inference(cnf_transformation,[],[f74]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_72,negated_conjecture,
% 7.67/1.51      ( v2_pre_topc(sK2) ),
% 7.67/1.51      inference(cnf_transformation,[],[f75]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_64,negated_conjecture,
% 7.67/1.51      ( ~ v2_struct_0(sK5) ),
% 7.67/1.51      inference(cnf_transformation,[],[f83]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_62,negated_conjecture,
% 7.67/1.51      ( ~ v2_struct_0(sK6) ),
% 7.67/1.51      inference(cnf_transformation,[],[f85]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_767,plain,
% 7.67/1.51      ( ~ l1_pre_topc(X1)
% 7.67/1.51      | v2_struct_0(X1)
% 7.67/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 7.67/1.51      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 7.67/1.51      | sP1(sK5,sK2,X0,sK6,X1)
% 7.67/1.51      | ~ v2_pre_topc(X1)
% 7.67/1.51      | ~ v1_funct_1(X0) ),
% 7.67/1.51      inference(global_propositional_subsumption,
% 7.67/1.51                [status(thm)],
% 7.67/1.51                [c_763,c_73,c_72,c_71,c_64,c_63,c_62,c_61]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_768,plain,
% 7.67/1.51      ( sP1(sK5,sK2,X0,sK6,X1)
% 7.67/1.51      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 7.67/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 7.67/1.51      | v2_struct_0(X1)
% 7.67/1.51      | ~ v2_pre_topc(X1)
% 7.67/1.51      | ~ l1_pre_topc(X1)
% 7.67/1.51      | ~ v1_funct_1(X0) ),
% 7.67/1.51      inference(renaming,[status(thm)],[c_767]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_955,plain,
% 7.67/1.51      ( sP0(X0,X1,X2,X3,X4)
% 7.67/1.51      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_tsep_1(X3,X4,X1),X0)
% 7.67/1.51      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 7.67/1.51      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))
% 7.67/1.51      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 7.67/1.51      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))))
% 7.67/1.51      | v2_struct_0(X6)
% 7.67/1.51      | ~ v2_pre_topc(X6)
% 7.67/1.51      | ~ l1_pre_topc(X6)
% 7.67/1.51      | ~ v1_funct_1(X5)
% 7.67/1.51      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)))
% 7.67/1.51      | X5 != X2
% 7.67/1.51      | X6 != X0
% 7.67/1.51      | sK5 != X4
% 7.67/1.51      | sK6 != X1
% 7.67/1.51      | sK2 != X3 ),
% 7.67/1.51      inference(resolution_lifted,[status(thm)],[c_14,c_768]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_956,plain,
% 7.67/1.51      ( sP0(X0,sK6,X1,sK2,sK5)
% 7.67/1.51      | ~ v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
% 7.67/1.51      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 7.67/1.51      | ~ v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))
% 7.67/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 7.67/1.51      | ~ m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
% 7.67/1.51      | v2_struct_0(X0)
% 7.67/1.51      | ~ v2_pre_topc(X0)
% 7.67/1.51      | ~ l1_pre_topc(X0)
% 7.67/1.51      | ~ v1_funct_1(X1)
% 7.67/1.51      | ~ v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) ),
% 7.67/1.51      inference(unflattening,[status(thm)],[c_955]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_2636,plain,
% 7.67/1.51      ( sP0(X0_54,sK6,X0_55,sK2,sK5)
% 7.67/1.51      | ~ v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_54)
% 7.67/1.51      | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
% 7.67/1.51      | ~ v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54))
% 7.67/1.51      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
% 7.67/1.51      | ~ m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54))))
% 7.67/1.51      | v2_struct_0(X0_54)
% 7.67/1.51      | ~ v2_pre_topc(X0_54)
% 7.67/1.51      | ~ l1_pre_topc(X0_54)
% 7.67/1.51      | ~ v1_funct_1(X0_55)
% 7.67/1.51      | ~ v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6))) ),
% 7.67/1.51      inference(subtyping,[status(esa)],[c_956]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3552,plain,
% 7.67/1.51      ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_54) != iProver_top
% 7.67/1.51      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.67/1.51      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54)))) != iProver_top
% 7.67/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.67/1.51      | v2_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | l1_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | v1_funct_1(X0_55) != iProver_top
% 7.67/1.51      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6))) != iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_2636]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_60,negated_conjecture,
% 7.67/1.51      ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
% 7.67/1.51      inference(cnf_transformation,[],[f87]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_2652,negated_conjecture,
% 7.67/1.51      ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
% 7.67/1.51      inference(subtyping,[status(esa)],[c_60]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3561,plain,
% 7.67/1.51      ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) != iProver_top
% 7.67/1.51      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.67/1.51      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.67/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.67/1.51      | v2_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | l1_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | v1_funct_1(X0_55) != iProver_top
% 7.67/1.51      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) != iProver_top ),
% 7.67/1.51      inference(light_normalisation,[status(thm)],[c_3552,c_2652]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_5193,plain,
% 7.67/1.51      ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) != iProver_top
% 7.67/1.51      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.67/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.67/1.51      | v2_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | l1_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | l1_struct_0(X0_54) != iProver_top
% 7.67/1.51      | l1_struct_0(sK2) != iProver_top
% 7.67/1.51      | v1_funct_1(X0_55) != iProver_top
% 7.67/1.51      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) != iProver_top ),
% 7.67/1.51      inference(superposition,[status(thm)],[c_3516,c_3561]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_2725,plain,
% 7.67/1.51      ( l1_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | l1_struct_0(X0_54) = iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_2676]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_6906,plain,
% 7.67/1.51      ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) != iProver_top
% 7.67/1.51      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.67/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.67/1.51      | v2_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | l1_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | v1_funct_1(X0_55) != iProver_top
% 7.67/1.51      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) != iProver_top ),
% 7.67/1.51      inference(global_propositional_subsumption,
% 7.67/1.51                [status(thm)],
% 7.67/1.51                [c_5193,c_76,c_2725,c_3824]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_6912,plain,
% 7.67/1.51      ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) != iProver_top
% 7.67/1.51      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.67/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.67/1.51      | v2_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | l1_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | l1_struct_0(X0_54) != iProver_top
% 7.67/1.51      | l1_struct_0(sK2) != iProver_top
% 7.67/1.51      | v1_funct_1(X0_55) != iProver_top
% 7.67/1.51      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) != iProver_top ),
% 7.67/1.51      inference(superposition,[status(thm)],[c_3517,c_6906]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_8657,plain,
% 7.67/1.51      ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) != iProver_top
% 7.67/1.51      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.67/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.67/1.51      | v2_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | l1_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | v1_funct_1(X0_55) != iProver_top
% 7.67/1.51      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) != iProver_top ),
% 7.67/1.51      inference(global_propositional_subsumption,
% 7.67/1.51                [status(thm)],
% 7.67/1.51                [c_6912,c_76,c_2725,c_3824]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_8663,plain,
% 7.67/1.51      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) != iProver_top
% 7.67/1.51      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.67/1.51      | v2_struct_0(sK3) = iProver_top
% 7.67/1.51      | v2_pre_topc(sK3) != iProver_top
% 7.67/1.51      | l1_pre_topc(sK3) != iProver_top
% 7.67/1.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) != iProver_top
% 7.67/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.67/1.51      inference(superposition,[status(thm)],[c_3541,c_8657]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_2,plain,
% 7.67/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.51      | v4_relat_1(X0,X1) ),
% 7.67/1.51      inference(cnf_transformation,[],[f50]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_0,plain,
% 7.67/1.51      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.67/1.51      inference(cnf_transformation,[],[f48]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_742,plain,
% 7.67/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.51      | ~ v1_relat_1(X0)
% 7.67/1.51      | k7_relat_1(X0,X1) = X0 ),
% 7.67/1.51      inference(resolution,[status(thm)],[c_2,c_0]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_1,plain,
% 7.67/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.51      | v1_relat_1(X0) ),
% 7.67/1.51      inference(cnf_transformation,[],[f49]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_746,plain,
% 7.67/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.51      | k7_relat_1(X0,X1) = X0 ),
% 7.67/1.51      inference(global_propositional_subsumption,
% 7.67/1.51                [status(thm)],
% 7.67/1.51                [c_742,c_2,c_1,c_0]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_2637,plain,
% 7.67/1.51      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 7.67/1.51      | k7_relat_1(X0_55,X0_56) = X0_55 ),
% 7.67/1.51      inference(subtyping,[status(esa)],[c_746]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3551,plain,
% 7.67/1.51      ( k7_relat_1(X0_55,X0_56) = X0_55
% 7.67/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_2637]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_6593,plain,
% 7.67/1.51      ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK4 ),
% 7.67/1.51      inference(superposition,[status(thm)],[c_3541,c_3551]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_25,plain,
% 7.67/1.51      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.67/1.51      inference(cnf_transformation,[],[f73]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_2661,plain,
% 7.67/1.51      ( m1_pre_topc(X0_54,X0_54) | ~ l1_pre_topc(X0_54) ),
% 7.67/1.51      inference(subtyping,[status(esa)],[c_25]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3528,plain,
% 7.67/1.51      ( m1_pre_topc(X0_54,X0_54) = iProver_top
% 7.67/1.51      | l1_pre_topc(X0_54) != iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_2661]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_6,plain,
% 7.67/1.51      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.67/1.51      | ~ m1_pre_topc(X3,X1)
% 7.67/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.67/1.51      | v2_struct_0(X1)
% 7.67/1.51      | v2_struct_0(X2)
% 7.67/1.51      | ~ v2_pre_topc(X2)
% 7.67/1.51      | ~ v2_pre_topc(X1)
% 7.67/1.51      | ~ l1_pre_topc(X1)
% 7.67/1.51      | ~ l1_pre_topc(X2)
% 7.67/1.51      | ~ v1_funct_1(X0)
% 7.67/1.51      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 7.67/1.51      inference(cnf_transformation,[],[f54]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_2674,plain,
% 7.67/1.51      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.67/1.51      | ~ m1_pre_topc(X2_54,X0_54)
% 7.67/1.51      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.67/1.51      | v2_struct_0(X0_54)
% 7.67/1.51      | v2_struct_0(X1_54)
% 7.67/1.51      | ~ v2_pre_topc(X0_54)
% 7.67/1.51      | ~ v2_pre_topc(X1_54)
% 7.67/1.51      | ~ l1_pre_topc(X0_54)
% 7.67/1.51      | ~ l1_pre_topc(X1_54)
% 7.67/1.51      | ~ v1_funct_1(X0_55)
% 7.67/1.51      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_55,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_55,X2_54) ),
% 7.67/1.51      inference(subtyping,[status(esa)],[c_6]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3515,plain,
% 7.67/1.51      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_55,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_55,X2_54)
% 7.67/1.51      | v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.67/1.51      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 7.67/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.67/1.51      | v2_struct_0(X1_54) = iProver_top
% 7.67/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.67/1.51      | v2_pre_topc(X1_54) != iProver_top
% 7.67/1.51      | v2_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | l1_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | l1_pre_topc(X1_54) != iProver_top
% 7.67/1.51      | v1_funct_1(X0_55) != iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_2674]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_4652,plain,
% 7.67/1.51      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK3,sK4,X0_54)
% 7.67/1.51      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.67/1.51      | m1_pre_topc(X0_54,sK2) != iProver_top
% 7.67/1.51      | v2_struct_0(sK3) = iProver_top
% 7.67/1.51      | v2_struct_0(sK2) = iProver_top
% 7.67/1.51      | v2_pre_topc(sK3) != iProver_top
% 7.67/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.67/1.51      | l1_pre_topc(sK3) != iProver_top
% 7.67/1.51      | l1_pre_topc(sK2) != iProver_top
% 7.67/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.67/1.51      inference(superposition,[status(thm)],[c_3541,c_3515]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_74,plain,
% 7.67/1.51      ( v2_struct_0(sK2) != iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_73]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_75,plain,
% 7.67/1.51      ( v2_pre_topc(sK2) = iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_72]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_5874,plain,
% 7.67/1.51      ( m1_pre_topc(X0_54,sK2) != iProver_top
% 7.67/1.51      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK3,sK4,X0_54) ),
% 7.67/1.51      inference(global_propositional_subsumption,
% 7.67/1.51                [status(thm)],
% 7.67/1.51                [c_4652,c_74,c_75,c_76,c_77,c_78,c_79,c_80,c_81]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_5875,plain,
% 7.67/1.51      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK3,sK4,X0_54)
% 7.67/1.51      | m1_pre_topc(X0_54,sK2) != iProver_top ),
% 7.67/1.51      inference(renaming,[status(thm)],[c_5874]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3,plain,
% 7.67/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.51      | ~ v1_funct_1(X0)
% 7.67/1.51      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.67/1.51      inference(cnf_transformation,[],[f51]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_2677,plain,
% 7.67/1.51      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 7.67/1.51      | ~ v1_funct_1(X0_55)
% 7.67/1.51      | k2_partfun1(X0_56,X1_56,X0_55,X2_56) = k7_relat_1(X0_55,X2_56) ),
% 7.67/1.51      inference(subtyping,[status(esa)],[c_3]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3512,plain,
% 7.67/1.51      ( k2_partfun1(X0_56,X1_56,X0_55,X2_56) = k7_relat_1(X0_55,X2_56)
% 7.67/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 7.67/1.51      | v1_funct_1(X0_55) != iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_2677]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3973,plain,
% 7.67/1.51      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_56) = k7_relat_1(sK4,X0_56)
% 7.67/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.67/1.51      inference(superposition,[status(thm)],[c_3541,c_3512]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_5009,plain,
% 7.67/1.51      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_56) = k7_relat_1(sK4,X0_56) ),
% 7.67/1.51      inference(global_propositional_subsumption,
% 7.67/1.51                [status(thm)],
% 7.67/1.51                [c_3973,c_80]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_5880,plain,
% 7.67/1.51      ( k2_tmap_1(sK2,sK3,sK4,X0_54) = k7_relat_1(sK4,u1_struct_0(X0_54))
% 7.67/1.51      | m1_pre_topc(X0_54,sK2) != iProver_top ),
% 7.67/1.51      inference(demodulation,[status(thm)],[c_5875,c_5009]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_5886,plain,
% 7.67/1.51      ( k2_tmap_1(sK2,sK3,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2))
% 7.67/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.67/1.51      inference(superposition,[status(thm)],[c_3528,c_5880]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_6166,plain,
% 7.67/1.51      ( k2_tmap_1(sK2,sK3,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 7.67/1.51      inference(global_propositional_subsumption,
% 7.67/1.51                [status(thm)],
% 7.67/1.51                [c_5886,c_76]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_6686,plain,
% 7.67/1.51      ( k2_tmap_1(sK2,sK3,sK4,sK2) = sK4 ),
% 7.67/1.51      inference(demodulation,[status(thm)],[c_6593,c_6166]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_8666,plain,
% 7.67/1.51      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 7.67/1.51      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.67/1.51      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.67/1.51      | v2_struct_0(sK3) = iProver_top
% 7.67/1.51      | v2_pre_topc(sK3) != iProver_top
% 7.67/1.51      | l1_pre_topc(sK3) != iProver_top
% 7.67/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.67/1.51      inference(light_normalisation,[status(thm)],[c_8663,c_6686]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_21,plain,
% 7.67/1.51      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) ),
% 7.67/1.51      inference(cnf_transformation,[],[f65]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_2664,plain,
% 7.67/1.51      ( ~ sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),X3_54,X0_54) ),
% 7.67/1.51      inference(subtyping,[status(esa)],[c_21]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3924,plain,
% 7.67/1.51      ( ~ sP0(sK3,X0_54,sK4,sK2,sK5)
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
% 7.67/1.51      inference(instantiation,[status(thm)],[c_2664]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_9277,plain,
% 7.67/1.51      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
% 7.67/1.51      inference(instantiation,[status(thm)],[c_3924]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_9281,plain,
% 7.67/1.51      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_9277]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_17,plain,
% 7.67/1.51      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) ),
% 7.67/1.51      inference(cnf_transformation,[],[f69]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_2668,plain,
% 7.67/1.51      ( ~ sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),X1_54,X0_54) ),
% 7.67/1.51      inference(subtyping,[status(esa)],[c_17]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_4477,plain,
% 7.67/1.51      ( ~ sP0(sK3,X0_54,sK4,sK2,X1_54)
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_54),X0_54,sK3) ),
% 7.67/1.51      inference(instantiation,[status(thm)],[c_2668]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_9287,plain,
% 7.67/1.51      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
% 7.67/1.51      inference(instantiation,[status(thm)],[c_4477]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_9289,plain,
% 7.67/1.51      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_9287]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_9400,plain,
% 7.67/1.51      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.67/1.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top ),
% 7.67/1.51      inference(global_propositional_subsumption,
% 7.67/1.51                [status(thm)],
% 7.67/1.51                [c_5616,c_76,c_77,c_78,c_79,c_80,c_81,c_82,c_176,c_807,
% 7.67/1.51                 c_3824,c_4100,c_8666,c_9281,c_9289]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_48,negated_conjecture,
% 7.67/1.51      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 7.67/1.51      | v5_pre_topc(sK4,sK2,sK3) ),
% 7.67/1.51      inference(cnf_transformation,[],[f99]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_98,plain,
% 7.67/1.51      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
% 7.67/1.51      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_32,negated_conjecture,
% 7.67/1.51      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 7.67/1.51      | v5_pre_topc(sK4,sK2,sK3) ),
% 7.67/1.51      inference(cnf_transformation,[],[f115]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_114,plain,
% 7.67/1.51      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
% 7.67/1.51      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_28,negated_conjecture,
% 7.67/1.51      ( v5_pre_topc(sK4,sK2,sK3)
% 7.67/1.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 7.67/1.51      inference(cnf_transformation,[],[f119]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_118,plain,
% 7.67/1.51      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.67/1.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_15,plain,
% 7.67/1.51      ( sP0(X0,X1,X2,X3,X4)
% 7.67/1.51      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
% 7.67/1.51      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
% 7.67/1.51      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
% 7.67/1.51      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
% 7.67/1.51      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 7.67/1.51      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
% 7.67/1.51      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
% 7.67/1.51      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
% 7.67/1.51      inference(cnf_transformation,[],[f71]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_2670,plain,
% 7.67/1.51      ( sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
% 7.67/1.51      | ~ v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),X1_54,X0_54)
% 7.67/1.51      | ~ v5_pre_topc(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),X3_54,X0_54)
% 7.67/1.51      | ~ v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),u1_struct_0(X1_54),u1_struct_0(X0_54))
% 7.67/1.51      | ~ v1_funct_2(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),u1_struct_0(X3_54),u1_struct_0(X0_54))
% 7.67/1.51      | ~ m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_55,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54))))
% 7.67/1.51      | ~ m1_subset_1(k2_tmap_1(X2_54,X0_54,X0_55,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X0_54))))
% 7.67/1.51      | ~ v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_55,X1_54))
% 7.67/1.51      | ~ v1_funct_1(k2_tmap_1(X2_54,X0_54,X0_55,X3_54)) ),
% 7.67/1.51      inference(subtyping,[status(esa)],[c_15]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3695,plain,
% 7.67/1.51      ( sP0(X0_54,sK6,X0_55,sK2,sK5)
% 7.67/1.51      | ~ v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK5),sK5,X0_54)
% 7.67/1.51      | ~ v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK6),sK6,X0_54)
% 7.67/1.51      | ~ v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK5),u1_struct_0(sK5),u1_struct_0(X0_54))
% 7.67/1.51      | ~ v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK6),u1_struct_0(sK6),u1_struct_0(X0_54))
% 7.67/1.51      | ~ m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54))))
% 7.67/1.51      | ~ m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_54))))
% 7.67/1.51      | ~ v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK5))
% 7.67/1.51      | ~ v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK6)) ),
% 7.67/1.51      inference(instantiation,[status(thm)],[c_2670]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3696,plain,
% 7.67/1.51      ( sP0(X0_54,sK6,X0_55,sK2,sK5) = iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK5),sK5,X0_54) != iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK6),sK6,X0_54) != iProver_top
% 7.67/1.51      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK5),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK6),u1_struct_0(sK6),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 7.67/1.51      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_54)))) != iProver_top
% 7.67/1.51      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK5)) != iProver_top
% 7.67/1.51      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK6)) != iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_3695]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3698,plain,
% 7.67/1.51      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 7.67/1.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.67/1.51      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 7.67/1.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.67/1.51      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 7.67/1.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 7.67/1.51      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 7.67/1.51      inference(instantiation,[status(thm)],[c_3696]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_10,plain,
% 7.67/1.51      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.67/1.51      | ~ sP0(X4,X3,X2,X1,X0)
% 7.67/1.51      | m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) ),
% 7.67/1.51      inference(cnf_transformation,[],[f62]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_1084,plain,
% 7.67/1.51      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.67/1.51      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 7.67/1.51      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 7.67/1.51      | m1_subset_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))))
% 7.67/1.51      | v2_struct_0(X6)
% 7.67/1.51      | ~ v2_pre_topc(X6)
% 7.67/1.51      | ~ l1_pre_topc(X6)
% 7.67/1.51      | ~ v1_funct_1(X5)
% 7.67/1.51      | X5 != X2
% 7.67/1.51      | X6 != X0
% 7.67/1.51      | sK5 != X4
% 7.67/1.51      | sK6 != X1
% 7.67/1.51      | sK2 != X3 ),
% 7.67/1.51      inference(resolution_lifted,[status(thm)],[c_10,c_768]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_1085,plain,
% 7.67/1.51      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 7.67/1.51      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 7.67/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 7.67/1.51      | m1_subset_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))))
% 7.67/1.51      | v2_struct_0(X0)
% 7.67/1.51      | ~ v2_pre_topc(X0)
% 7.67/1.51      | ~ l1_pre_topc(X0)
% 7.67/1.51      | ~ v1_funct_1(X1) ),
% 7.67/1.51      inference(unflattening,[status(thm)],[c_1084]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_2632,plain,
% 7.67/1.51      ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
% 7.67/1.51      | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
% 7.67/1.51      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
% 7.67/1.51      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54))))
% 7.67/1.51      | v2_struct_0(X0_54)
% 7.67/1.51      | ~ v2_pre_topc(X0_54)
% 7.67/1.51      | ~ l1_pre_topc(X0_54)
% 7.67/1.51      | ~ v1_funct_1(X0_55) ),
% 7.67/1.51      inference(subtyping,[status(esa)],[c_1085]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3556,plain,
% 7.67/1.51      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 7.67/1.51      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.67/1.51      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54)))) = iProver_top
% 7.67/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.67/1.51      | v2_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | l1_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | v1_funct_1(X0_55) != iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_2632]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3560,plain,
% 7.67/1.51      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 7.67/1.51      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.67/1.51      | m1_subset_1(k2_tmap_1(sK2,X0_54,X0_55,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) = iProver_top
% 7.67/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.67/1.51      | v2_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | l1_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | v1_funct_1(X0_55) != iProver_top ),
% 7.67/1.51      inference(light_normalisation,[status(thm)],[c_3556,c_2652]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_11,plain,
% 7.67/1.51      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.67/1.51      | ~ sP0(X4,X3,X2,X1,X0)
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) ),
% 7.67/1.51      inference(cnf_transformation,[],[f61]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_1054,plain,
% 7.67/1.51      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),k1_tsep_1(X3,X4,X1),X0)
% 7.67/1.51      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 7.67/1.51      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 7.67/1.51      | v2_struct_0(X6)
% 7.67/1.51      | ~ v2_pre_topc(X6)
% 7.67/1.51      | ~ l1_pre_topc(X6)
% 7.67/1.51      | ~ v1_funct_1(X5)
% 7.67/1.51      | X5 != X2
% 7.67/1.51      | X6 != X0
% 7.67/1.51      | sK5 != X4
% 7.67/1.51      | sK6 != X1
% 7.67/1.51      | sK2 != X3 ),
% 7.67/1.51      inference(resolution_lifted,[status(thm)],[c_11,c_768]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_1055,plain,
% 7.67/1.51      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0)
% 7.67/1.51      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 7.67/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 7.67/1.51      | v2_struct_0(X0)
% 7.67/1.51      | ~ v2_pre_topc(X0)
% 7.67/1.51      | ~ l1_pre_topc(X0)
% 7.67/1.51      | ~ v1_funct_1(X1) ),
% 7.67/1.51      inference(unflattening,[status(thm)],[c_1054]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_2633,plain,
% 7.67/1.51      ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_54)
% 7.67/1.51      | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
% 7.67/1.51      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
% 7.67/1.51      | v2_struct_0(X0_54)
% 7.67/1.51      | ~ v2_pre_topc(X0_54)
% 7.67/1.51      | ~ l1_pre_topc(X0_54)
% 7.67/1.51      | ~ v1_funct_1(X0_55) ),
% 7.67/1.51      inference(subtyping,[status(esa)],[c_1055]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3555,plain,
% 7.67/1.51      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),X0_54) = iProver_top
% 7.67/1.51      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.67/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.67/1.51      | v2_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | l1_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | v1_funct_1(X0_55) != iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_2633]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3558,plain,
% 7.67/1.51      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,X0_54) = iProver_top
% 7.67/1.51      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.67/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.67/1.51      | v2_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | l1_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | v1_funct_1(X0_55) != iProver_top ),
% 7.67/1.51      inference(light_normalisation,[status(thm)],[c_3555,c_2652]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_4558,plain,
% 7.67/1.51      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 7.67/1.51      | sP0(X0_54,sK6,k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,sK5) != iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,X0_54,k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2),sK2,X0_54) = iProver_top
% 7.67/1.51      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.67/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.67/1.51      | v2_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | l1_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | v1_funct_1(X0_55) != iProver_top
% 7.67/1.51      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) != iProver_top ),
% 7.67/1.51      inference(superposition,[status(thm)],[c_3560,c_3558]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_12,plain,
% 7.67/1.51      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.67/1.51      | ~ sP0(X4,X3,X2,X1,X0)
% 7.67/1.51      | v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) ),
% 7.67/1.51      inference(cnf_transformation,[],[f60]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_1024,plain,
% 7.67/1.51      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.67/1.51      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 7.67/1.51      | v1_funct_2(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)),u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X0))
% 7.67/1.51      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 7.67/1.51      | v2_struct_0(X6)
% 7.67/1.51      | ~ v2_pre_topc(X6)
% 7.67/1.51      | ~ l1_pre_topc(X6)
% 7.67/1.51      | ~ v1_funct_1(X5)
% 7.67/1.51      | X5 != X2
% 7.67/1.51      | X6 != X0
% 7.67/1.51      | sK5 != X4
% 7.67/1.51      | sK6 != X1
% 7.67/1.51      | sK2 != X3 ),
% 7.67/1.51      inference(resolution_lifted,[status(thm)],[c_12,c_768]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_1025,plain,
% 7.67/1.51      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 7.67/1.51      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 7.67/1.51      | v1_funct_2(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0))
% 7.67/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 7.67/1.51      | v2_struct_0(X0)
% 7.67/1.51      | ~ v2_pre_topc(X0)
% 7.67/1.51      | ~ l1_pre_topc(X0)
% 7.67/1.51      | ~ v1_funct_1(X1) ),
% 7.67/1.51      inference(unflattening,[status(thm)],[c_1024]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_2634,plain,
% 7.67/1.51      ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
% 7.67/1.51      | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
% 7.67/1.51      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54))
% 7.67/1.51      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
% 7.67/1.51      | v2_struct_0(X0_54)
% 7.67/1.51      | ~ v2_pre_topc(X0_54)
% 7.67/1.51      | ~ l1_pre_topc(X0_54)
% 7.67/1.51      | ~ v1_funct_1(X0_55) ),
% 7.67/1.51      inference(subtyping,[status(esa)],[c_1025]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3554,plain,
% 7.67/1.51      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 7.67/1.51      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(X0_54)) = iProver_top
% 7.67/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.67/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.67/1.51      | v2_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | l1_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | v1_funct_1(X0_55) != iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_2634]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3559,plain,
% 7.67/1.51      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 7.67/1.51      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | v1_funct_2(k2_tmap_1(sK2,X0_54,X0_55,sK2),u1_struct_0(sK2),u1_struct_0(X0_54)) = iProver_top
% 7.67/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.67/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.67/1.51      | v2_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | l1_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | v1_funct_1(X0_55) != iProver_top ),
% 7.67/1.51      inference(light_normalisation,[status(thm)],[c_3554,c_2652]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_13,plain,
% 7.67/1.51      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.67/1.51      | ~ sP0(X4,X3,X2,X1,X0)
% 7.67/1.51      | v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
% 7.67/1.51      inference(cnf_transformation,[],[f59]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_994,plain,
% 7.67/1.51      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.67/1.51      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
% 7.67/1.51      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
% 7.67/1.51      | v2_struct_0(X6)
% 7.67/1.51      | ~ v2_pre_topc(X6)
% 7.67/1.51      | ~ l1_pre_topc(X6)
% 7.67/1.51      | ~ v1_funct_1(X5)
% 7.67/1.51      | v1_funct_1(k2_tmap_1(X3,X0,X2,k1_tsep_1(X3,X4,X1)))
% 7.67/1.51      | X5 != X2
% 7.67/1.51      | X6 != X0
% 7.67/1.51      | sK5 != X4
% 7.67/1.51      | sK6 != X1
% 7.67/1.51      | sK2 != X3 ),
% 7.67/1.51      inference(resolution_lifted,[status(thm)],[c_13,c_768]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_995,plain,
% 7.67/1.51      ( ~ sP0(X0,sK6,X1,sK2,sK5)
% 7.67/1.51      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 7.67/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 7.67/1.51      | v2_struct_0(X0)
% 7.67/1.51      | ~ v2_pre_topc(X0)
% 7.67/1.51      | ~ l1_pre_topc(X0)
% 7.67/1.51      | ~ v1_funct_1(X1)
% 7.67/1.51      | v1_funct_1(k2_tmap_1(sK2,X0,X1,k1_tsep_1(sK2,sK5,sK6))) ),
% 7.67/1.51      inference(unflattening,[status(thm)],[c_994]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_2635,plain,
% 7.67/1.51      ( ~ sP0(X0_54,sK6,X0_55,sK2,sK5)
% 7.67/1.51      | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54))
% 7.67/1.51      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54))))
% 7.67/1.51      | v2_struct_0(X0_54)
% 7.67/1.51      | ~ v2_pre_topc(X0_54)
% 7.67/1.51      | ~ l1_pre_topc(X0_54)
% 7.67/1.51      | ~ v1_funct_1(X0_55)
% 7.67/1.51      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6))) ),
% 7.67/1.51      inference(subtyping,[status(esa)],[c_995]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3553,plain,
% 7.67/1.51      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 7.67/1.51      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.67/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.67/1.51      | v2_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | l1_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | v1_funct_1(X0_55) != iProver_top
% 7.67/1.51      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_2635]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3557,plain,
% 7.67/1.51      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 7.67/1.51      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.67/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.67/1.51      | v2_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | l1_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | v1_funct_1(X0_55) != iProver_top
% 7.67/1.51      | v1_funct_1(k2_tmap_1(sK2,X0_54,X0_55,sK2)) = iProver_top ),
% 7.67/1.51      inference(light_normalisation,[status(thm)],[c_3553,c_2652]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_6989,plain,
% 7.67/1.51      ( v1_funct_1(X0_55) != iProver_top
% 7.67/1.51      | l1_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | v2_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.67/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.67/1.51      | sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 7.67/1.51      | sP0(X0_54,sK6,k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,sK5) != iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,X0_54,k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2),sK2,X0_54) = iProver_top
% 7.67/1.51      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top ),
% 7.67/1.51      inference(global_propositional_subsumption,
% 7.67/1.51                [status(thm)],
% 7.67/1.51                [c_4558,c_3559,c_3557]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_6990,plain,
% 7.67/1.51      ( sP0(X0_54,sK6,X0_55,sK2,sK5) != iProver_top
% 7.67/1.51      | sP0(X0_54,sK6,k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2,sK5) != iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,X0_54,k2_tmap_1(sK2,X0_54,X0_55,sK2),sK2),sK2,X0_54) = iProver_top
% 7.67/1.51      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.67/1.51      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 7.67/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.67/1.51      | v2_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | l1_pre_topc(X0_54) != iProver_top
% 7.67/1.51      | v1_funct_1(X0_55) != iProver_top ),
% 7.67/1.51      inference(renaming,[status(thm)],[c_6989]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_9183,plain,
% 7.67/1.51      ( sP0(sK3,sK6,k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK5) != iProver_top
% 7.67/1.51      | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.67/1.51      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) = iProver_top
% 7.67/1.51      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.67/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.67/1.51      | v2_struct_0(sK3) = iProver_top
% 7.67/1.51      | v2_pre_topc(sK3) != iProver_top
% 7.67/1.51      | l1_pre_topc(sK3) != iProver_top
% 7.67/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.67/1.51      inference(superposition,[status(thm)],[c_6686,c_6990]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_9199,plain,
% 7.67/1.51      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 7.67/1.51      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.67/1.51      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.67/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.67/1.51      | v2_struct_0(sK3) = iProver_top
% 7.67/1.51      | v2_pre_topc(sK3) != iProver_top
% 7.67/1.51      | l1_pre_topc(sK3) != iProver_top
% 7.67/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.67/1.51      inference(light_normalisation,[status(thm)],[c_9183,c_6686]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_9404,plain,
% 7.67/1.51      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top ),
% 7.67/1.51      inference(global_propositional_subsumption,
% 7.67/1.51                [status(thm)],
% 7.67/1.51                [c_9400,c_76,c_77,c_78,c_79,c_80,c_81,c_82,c_98,c_114,
% 7.67/1.51                 c_118,c_176,c_807,c_818,c_3660,c_3698,c_3732,c_3824,
% 7.67/1.51                 c_4055,c_4100,c_4510,c_4956,c_9199]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_2651,negated_conjecture,
% 7.67/1.51      ( m1_pre_topc(sK6,sK2) ),
% 7.67/1.51      inference(subtyping,[status(esa)],[c_61]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_3537,plain,
% 7.67/1.51      ( m1_pre_topc(sK6,sK2) = iProver_top ),
% 7.67/1.51      inference(predicate_to_equality,[status(thm)],[c_2651]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_5884,plain,
% 7.67/1.51      ( k2_tmap_1(sK2,sK3,sK4,sK6) = k7_relat_1(sK4,u1_struct_0(sK6)) ),
% 7.67/1.51      inference(superposition,[status(thm)],[c_3537,c_5880]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_9408,plain,
% 7.67/1.51      ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top ),
% 7.67/1.51      inference(light_normalisation,[status(thm)],[c_9404,c_5884]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_5980,plain,
% 7.67/1.51      ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top
% 7.67/1.51      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.67/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.67/1.51      | l1_struct_0(sK6) != iProver_top
% 7.67/1.51      | l1_struct_0(sK3) != iProver_top
% 7.67/1.51      | l1_struct_0(sK2) != iProver_top
% 7.67/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.67/1.51      inference(superposition,[status(thm)],[c_5884,c_3517]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(contradiction,plain,
% 7.67/1.51      ( $false ),
% 7.67/1.51      inference(minisat,
% 7.67/1.51                [status(thm)],
% 7.67/1.51                [c_9408,c_5980,c_4100,c_3824,c_807,c_176,c_82,c_81,c_80,
% 7.67/1.51                 c_79,c_76]) ).
% 7.67/1.51  
% 7.67/1.51  
% 7.67/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.67/1.51  
% 7.67/1.51  ------                               Statistics
% 7.67/1.51  
% 7.67/1.51  ------ General
% 7.67/1.51  
% 7.67/1.51  abstr_ref_over_cycles:                  0
% 7.67/1.51  abstr_ref_under_cycles:                 0
% 7.67/1.51  gc_basic_clause_elim:                   0
% 7.67/1.51  forced_gc_time:                         0
% 7.67/1.51  parsing_time:                           0.013
% 7.67/1.51  unif_index_cands_time:                  0.
% 7.67/1.51  unif_index_add_time:                    0.
% 7.67/1.51  orderings_time:                         0.
% 7.67/1.51  out_proof_time:                         0.033
% 7.67/1.51  total_time:                             0.507
% 7.67/1.51  num_of_symbols:                         59
% 7.67/1.51  num_of_terms:                           8380
% 7.67/1.51  
% 7.67/1.51  ------ Preprocessing
% 7.67/1.51  
% 7.67/1.51  num_of_splits:                          0
% 7.67/1.51  num_of_split_atoms:                     0
% 7.67/1.51  num_of_reused_defs:                     0
% 7.67/1.51  num_eq_ax_congr_red:                    29
% 7.67/1.51  num_of_sem_filtered_clauses:            1
% 7.67/1.51  num_of_subtypes:                        5
% 7.67/1.51  monotx_restored_types:                  0
% 7.67/1.51  sat_num_of_epr_types:                   0
% 7.67/1.51  sat_num_of_non_cyclic_types:            0
% 7.67/1.51  sat_guarded_non_collapsed_types:        1
% 7.67/1.51  num_pure_diseq_elim:                    0
% 7.67/1.51  simp_replaced_by:                       0
% 7.67/1.51  res_preprocessed:                       233
% 7.67/1.51  prep_upred:                             0
% 7.67/1.51  prep_unflattend:                        172
% 7.67/1.51  smt_new_axioms:                         0
% 7.67/1.51  pred_elim_cands:                        10
% 7.67/1.51  pred_elim:                              4
% 7.67/1.51  pred_elim_cl:                           4
% 7.67/1.51  pred_elim_cycles:                       8
% 7.67/1.51  merged_defs:                            0
% 7.67/1.51  merged_defs_ncl:                        0
% 7.67/1.51  bin_hyper_res:                          0
% 7.67/1.51  prep_cycles:                            4
% 7.67/1.51  pred_elim_time:                         0.061
% 7.67/1.51  splitting_time:                         0.
% 7.67/1.51  sem_filter_time:                        0.
% 7.67/1.51  monotx_time:                            0.
% 7.67/1.51  subtype_inf_time:                       0.001
% 7.67/1.51  
% 7.67/1.51  ------ Problem properties
% 7.67/1.51  
% 7.67/1.51  clauses:                                46
% 7.67/1.51  conjectures:                            23
% 7.67/1.51  epr:                                    14
% 7.67/1.51  horn:                                   32
% 7.67/1.51  ground:                                 23
% 7.67/1.51  unary:                                  14
% 7.67/1.51  binary:                                 19
% 7.67/1.51  lits:                                   151
% 7.67/1.51  lits_eq:                                4
% 7.67/1.51  fd_pure:                                0
% 7.67/1.51  fd_pseudo:                              0
% 7.67/1.51  fd_cond:                                0
% 7.67/1.51  fd_pseudo_cond:                         0
% 7.67/1.51  ac_symbols:                             0
% 7.67/1.51  
% 7.67/1.51  ------ Propositional Solver
% 7.67/1.51  
% 7.67/1.51  prop_solver_calls:                      32
% 7.67/1.51  prop_fast_solver_calls:                 2972
% 7.67/1.51  smt_solver_calls:                       0
% 7.67/1.51  smt_fast_solver_calls:                  0
% 7.67/1.51  prop_num_of_clauses:                    2995
% 7.67/1.51  prop_preprocess_simplified:             10091
% 7.67/1.51  prop_fo_subsumed:                       239
% 7.67/1.51  prop_solver_time:                       0.
% 7.67/1.51  smt_solver_time:                        0.
% 7.67/1.51  smt_fast_solver_time:                   0.
% 7.67/1.51  prop_fast_solver_time:                  0.
% 7.67/1.51  prop_unsat_core_time:                   0.
% 7.67/1.51  
% 7.67/1.51  ------ QBF
% 7.67/1.51  
% 7.67/1.51  qbf_q_res:                              0
% 7.67/1.51  qbf_num_tautologies:                    0
% 7.67/1.51  qbf_prep_cycles:                        0
% 7.67/1.51  
% 7.67/1.51  ------ BMC1
% 7.67/1.51  
% 7.67/1.51  bmc1_current_bound:                     -1
% 7.67/1.51  bmc1_last_solved_bound:                 -1
% 7.67/1.51  bmc1_unsat_core_size:                   -1
% 7.67/1.51  bmc1_unsat_core_parents_size:           -1
% 7.67/1.51  bmc1_merge_next_fun:                    0
% 7.67/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.67/1.51  
% 7.67/1.51  ------ Instantiation
% 7.67/1.51  
% 7.67/1.51  inst_num_of_clauses:                    924
% 7.67/1.51  inst_num_in_passive:                    390
% 7.67/1.51  inst_num_in_active:                     504
% 7.67/1.51  inst_num_in_unprocessed:                30
% 7.67/1.51  inst_num_of_loops:                      570
% 7.67/1.51  inst_num_of_learning_restarts:          0
% 7.67/1.51  inst_num_moves_active_passive:          60
% 7.67/1.51  inst_lit_activity:                      0
% 7.67/1.51  inst_lit_activity_moves:                0
% 7.67/1.51  inst_num_tautologies:                   0
% 7.67/1.51  inst_num_prop_implied:                  0
% 7.67/1.51  inst_num_existing_simplified:           0
% 7.67/1.51  inst_num_eq_res_simplified:             0
% 7.67/1.51  inst_num_child_elim:                    0
% 7.67/1.51  inst_num_of_dismatching_blockings:      640
% 7.67/1.51  inst_num_of_non_proper_insts:           1348
% 7.67/1.51  inst_num_of_duplicates:                 0
% 7.67/1.51  inst_inst_num_from_inst_to_res:         0
% 7.67/1.51  inst_dismatching_checking_time:         0.
% 7.67/1.51  
% 7.67/1.51  ------ Resolution
% 7.67/1.51  
% 7.67/1.51  res_num_of_clauses:                     0
% 7.67/1.51  res_num_in_passive:                     0
% 7.67/1.51  res_num_in_active:                      0
% 7.67/1.51  res_num_of_loops:                       237
% 7.67/1.51  res_forward_subset_subsumed:            101
% 7.67/1.51  res_backward_subset_subsumed:           0
% 7.67/1.51  res_forward_subsumed:                   0
% 7.67/1.51  res_backward_subsumed:                  0
% 7.67/1.51  res_forward_subsumption_resolution:     0
% 7.67/1.51  res_backward_subsumption_resolution:    0
% 7.67/1.51  res_clause_to_clause_subsumption:       513
% 7.67/1.51  res_orphan_elimination:                 0
% 7.67/1.51  res_tautology_del:                      190
% 7.67/1.51  res_num_eq_res_simplified:              0
% 7.67/1.51  res_num_sel_changes:                    0
% 7.67/1.51  res_moves_from_active_to_pass:          0
% 7.67/1.51  
% 7.67/1.51  ------ Superposition
% 7.67/1.51  
% 7.67/1.51  sup_time_total:                         0.
% 7.67/1.51  sup_time_generating:                    0.
% 7.67/1.51  sup_time_sim_full:                      0.
% 7.67/1.51  sup_time_sim_immed:                     0.
% 7.67/1.51  
% 7.67/1.51  sup_num_of_clauses:                     129
% 7.67/1.51  sup_num_in_active:                      90
% 7.67/1.51  sup_num_in_passive:                     39
% 7.67/1.51  sup_num_of_loops:                       113
% 7.67/1.51  sup_fw_superposition:                   89
% 7.67/1.51  sup_bw_superposition:                   54
% 7.67/1.51  sup_immediate_simplified:               48
% 7.67/1.51  sup_given_eliminated:                   1
% 7.67/1.51  comparisons_done:                       0
% 7.67/1.51  comparisons_avoided:                    0
% 7.67/1.51  
% 7.67/1.51  ------ Simplifications
% 7.67/1.51  
% 7.67/1.51  
% 7.67/1.51  sim_fw_subset_subsumed:                 4
% 7.67/1.51  sim_bw_subset_subsumed:                 7
% 7.67/1.51  sim_fw_subsumed:                        10
% 7.67/1.51  sim_bw_subsumed:                        7
% 7.67/1.51  sim_fw_subsumption_res:                 0
% 7.67/1.51  sim_bw_subsumption_res:                 0
% 7.67/1.51  sim_tautology_del:                      14
% 7.67/1.51  sim_eq_tautology_del:                   10
% 7.67/1.51  sim_eq_res_simp:                        0
% 7.67/1.51  sim_fw_demodulated:                     10
% 7.67/1.51  sim_bw_demodulated:                     17
% 7.67/1.51  sim_light_normalised:                   47
% 7.67/1.51  sim_joinable_taut:                      0
% 7.67/1.51  sim_joinable_simp:                      0
% 7.67/1.51  sim_ac_normalised:                      0
% 7.67/1.51  sim_smt_subsumption:                    0
% 7.67/1.51  
%------------------------------------------------------------------------------
