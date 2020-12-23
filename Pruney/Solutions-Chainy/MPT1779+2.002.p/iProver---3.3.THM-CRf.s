%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:42 EST 2020

% Result     : Theorem 11.56s
% Output     : CNFRefutation 11.56s
% Verified   : 
% Statistics : Number of formulae       :  251 (13573 expanded)
%              Number of clauses        :  180 (2992 expanded)
%              Number of leaves         :   16 (5927 expanded)
%              Depth                    :   24
%              Number of atoms          : 1688 (294354 expanded)
%              Number of equality atoms :  559 (4299 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal clause size      :   50 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X4,X2)
                          & m1_pre_topc(X2,X3) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                                & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                                & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) )
                             => ( m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                                & v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                                & v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                                & v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
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
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X4,X2)
                            & m1_pre_topc(X2,X3) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => ( ( m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                  & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                                  & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                                  & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) )
                               => ( m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                                  & v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                                  & v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                                  & v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                            | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                            | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                          & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X2)
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                            | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                            | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                          & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X2)
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
            | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
            | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
            | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
          & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
          | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,sK5),X4,X1)
          | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,sK5),u1_struct_0(X4),u1_struct_0(X1))
          | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,sK5)) )
        & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,sK5),X2,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,sK5),u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,sK5))
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
              & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
              & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X5) )
          & m1_pre_topc(X4,X2)
          & m1_pre_topc(X2,X3)
          & m1_pre_topc(X4,X0)
          & ~ v2_struct_0(X4) )
     => ( ? [X5] :
            ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
              | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,sK4,X5),sK4,X1)
              | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,sK4,X5),u1_struct_0(sK4),u1_struct_0(X1))
              | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,sK4,X5)) )
            & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
            & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_pre_topc(sK4,X2)
        & m1_pre_topc(X2,X3)
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                    | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                    | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                  & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                  & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X5) )
              & m1_pre_topc(X4,X2)
              & m1_pre_topc(X2,X3)
              & m1_pre_topc(X4,X0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k3_tmap_1(X0,X1,sK3,X4,X5),X4,X1)
                  | ~ v1_funct_2(k3_tmap_1(X0,X1,sK3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                  | ~ v1_funct_1(k3_tmap_1(X0,X1,sK3,X4,X5)) )
                & m1_subset_1(k3_tmap_1(X0,X1,sK3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v5_pre_topc(k3_tmap_1(X0,X1,sK3,X2,X5),X2,X1)
                & v1_funct_2(k3_tmap_1(X0,X1,sK3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(k3_tmap_1(X0,X1,sK3,X2,X5))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
                & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_pre_topc(X4,X2)
            & m1_pre_topc(X2,sK3)
            & m1_pre_topc(X4,X0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                      & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                      & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X5) )
                  & m1_pre_topc(X4,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X4,X0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                      | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                      | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                    & m1_subset_1(k3_tmap_1(X0,X1,X3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                    & v5_pre_topc(k3_tmap_1(X0,X1,X3,sK2,X5),sK2,X1)
                    & v1_funct_2(k3_tmap_1(X0,X1,X3,sK2,X5),u1_struct_0(sK2),u1_struct_0(X1))
                    & v1_funct_1(k3_tmap_1(X0,X1,X3,sK2,X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_pre_topc(X4,sK2)
                & m1_pre_topc(sK2,X3)
                & m1_pre_topc(X4,X0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                            | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                            | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                          & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X2)
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k3_tmap_1(X0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,sK1,X3,X4,X5),X4,sK1)
                          | ~ v1_funct_2(k3_tmap_1(X0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1))
                          | ~ v1_funct_1(k3_tmap_1(X0,sK1,X3,X4,X5)) )
                        & m1_subset_1(k3_tmap_1(X0,sK1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                        & v5_pre_topc(k3_tmap_1(X0,sK1,X3,X2,X5),X2,sK1)
                        & v1_funct_2(k3_tmap_1(X0,sK1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(sK1))
                        & v1_funct_1(k3_tmap_1(X0,sK1,X3,X2,X5))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                        & v1_funct_1(X5) )
                    & m1_pre_topc(X4,X2)
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X4,X0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                              | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                              | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                              | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                            & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_pre_topc(X4,X2)
                        & m1_pre_topc(X2,X3)
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
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
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k3_tmap_1(sK0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k3_tmap_1(sK0,X1,X3,X4,X5),X4,X1)
                            | ~ v1_funct_2(k3_tmap_1(sK0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                            | ~ v1_funct_1(k3_tmap_1(sK0,X1,X3,X4,X5)) )
                          & m1_subset_1(k3_tmap_1(sK0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(sK0,X1,X3,X2,X5),X2,X1)
                          & v1_funct_2(k3_tmap_1(sK0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X2)
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) )
    & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK2)
    & m1_pre_topc(sK2,sK3)
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f30,f37,f36,f35,f34,f33,f32])).

fof(f67,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f74,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f19,plain,(
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
    inference(flattening,[],[f19])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(cnf_transformation,[],[f38])).

fof(f72,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f17,plain,(
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
    inference(flattening,[],[f17])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(flattening,[],[f23])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
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
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
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
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
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
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
    inference(cnf_transformation,[],[f22])).

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

fof(f12,plain,(
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

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
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
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f38])).

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
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(flattening,[],[f27])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,X2,X1)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
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
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,(
    v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_473,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1080,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_472,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1081,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_472])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_483,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(X2_51,X0_51)
    | m1_pre_topc(X2_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1070,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_pre_topc(X2_51,X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_2085,plain,
    ( m1_pre_topc(X0_51,sK2) != iProver_top
    | m1_pre_topc(X0_51,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1081,c_1070])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_38,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_39,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_46,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_49,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1674,plain,
    ( ~ m1_pre_topc(X0_51,sK2)
    | m1_pre_topc(X0_51,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_1675,plain,
    ( m1_pre_topc(X0_51,sK2) != iProver_top
    | m1_pre_topc(X0_51,sK3) = iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1674])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_490,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1459,plain,
    ( ~ m1_pre_topc(sK3,X0_51)
    | ~ l1_pre_topc(X0_51)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_490])).

cnf(c_2009,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_2010,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2009])).

cnf(c_469,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1084,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_469])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_491,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51)
    | v2_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1062,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_2076,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1084,c_1062])).

cnf(c_2642,plain,
    ( m1_pre_topc(X0_51,sK2) != iProver_top
    | m1_pre_topc(X0_51,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2085,c_38,c_39,c_46,c_49,c_1675,c_2010,c_2076])).

cnf(c_2648,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1080,c_2642])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_480,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1073,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_488,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X2_51,X3_51)
    | ~ m1_pre_topc(X0_51,X3_51)
    | ~ m1_pre_topc(X2_51,X0_51)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(X3_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X3_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X3_51)
    | ~ v1_funct_1(X0_49)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_49,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_49) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1065,plain,
    ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_49,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_49)
    | v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_pre_topc(X0_51,X3_51) != iProver_top
    | m1_pre_topc(X2_51,X3_51) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X3_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X3_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X3_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_2413,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X0_51,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1073,c_1065])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_40,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_41,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_42,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_54,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_55,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3857,plain,
    ( l1_pre_topc(X1_51) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X0_51,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2413,c_40,c_41,c_42,c_54,c_55])).

cnf(c_3858,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X0_51,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_3857])).

cnf(c_3868,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)) = k3_tmap_1(sK3,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2648,c_3858])).

cnf(c_4,plain,
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
    inference(cnf_transformation,[],[f43])).

cnf(c_489,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X2_51,X0_51)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X0_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X0_51)
    | ~ v1_funct_1(X0_49)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_49,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_49,X2_51) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1064,plain,
    ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_49,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_49,X2_51)
    | v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_2193,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0_51)
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1073,c_1064])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_43,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_44,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1453,plain,
    ( ~ m1_pre_topc(sK2,X0_51)
    | ~ l1_pre_topc(X0_51)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_490])).

cnf(c_2006,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1453])).

cnf(c_2007,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2006])).

cnf(c_2074,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) = iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1081,c_1062])).

cnf(c_3703,plain,
    ( m1_pre_topc(X0_51,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2193,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_46,c_54,c_55,c_2007,c_2010,c_2074,c_2076])).

cnf(c_3704,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0_51)
    | m1_pre_topc(X0_51,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3703])).

cnf(c_3709,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)) = k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4) ),
    inference(superposition,[status(thm)],[c_1080,c_3704])).

cnf(c_3869,plain,
    ( k3_tmap_1(sK3,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) = k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4)
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3868,c_3709])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_45,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_50,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5025,plain,
    ( k3_tmap_1(sK3,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) = k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3869,c_38,c_39,c_45,c_46,c_49,c_50,c_2010,c_2076])).

cnf(c_467,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1086,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_476,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1077,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_2414,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK3,X0_51,sK5)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X0_51,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1077,c_1065])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_51,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_52,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3405,plain,
    ( l1_pre_topc(X1_51) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK3,X0_51,sK5)
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X0_51,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2414,c_40,c_41,c_42,c_51,c_52])).

cnf(c_3406,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK3,X0_51,sK5)
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X0_51,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_3405])).

cnf(c_3415,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,sK5)
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1086,c_3406])).

cnf(c_2194,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0_51)) = k2_tmap_1(sK3,sK1,sK5,X0_51)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1077,c_1064])).

cnf(c_3169,plain,
    ( m1_pre_topc(X0_51,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0_51)) = k2_tmap_1(sK3,sK1,sK5,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2194,c_38,c_39,c_40,c_41,c_42,c_45,c_46,c_51,c_52,c_2010,c_2076])).

cnf(c_3170,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0_51)) = k2_tmap_1(sK3,sK1,sK5,X0_51)
    | m1_pre_topc(X0_51,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3169])).

cnf(c_3175,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK5,sK2) ),
    inference(superposition,[status(thm)],[c_1081,c_3170])).

cnf(c_3418,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k2_tmap_1(sK3,sK1,sK5,sK2)
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3415,c_3175])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_37,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4118,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k2_tmap_1(sK3,sK1,sK5,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3418,c_37,c_38,c_39,c_46,c_49])).

cnf(c_5027,plain,
    ( k3_tmap_1(sK3,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) ),
    inference(light_normalisation,[status(thm)],[c_5025,c_4118])).

cnf(c_9,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k2_tmap_1(X2,X1,X4,X3)),k2_tmap_1(X2,X1,X4,X0))
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_484,plain,
    ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k3_tmap_1(X2_51,X1_51,X3_51,X0_51,k2_tmap_1(X2_51,X1_51,X0_49,X3_51)),k2_tmap_1(X2_51,X1_51,X0_49,X0_51))
    | ~ v1_funct_2(X0_49,u1_struct_0(X2_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X0_51,X3_51)
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_pre_topc(X0_51,X2_51)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
    | v2_struct_0(X2_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X3_51)
    | v2_struct_0(X0_51)
    | ~ l1_pre_topc(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1069,plain,
    ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k3_tmap_1(X2_51,X1_51,X3_51,X0_51,k2_tmap_1(X2_51,X1_51,X0_49,X3_51)),k2_tmap_1(X2_51,X1_51,X0_49,X0_51)) = iProver_top
    | v1_funct_2(X0_49,u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X3_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X3_51) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(X3_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_484])).

cnf(c_5031,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4)) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5027,c_1069])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_47,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_53,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7744,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5031,c_38,c_39,c_40,c_41,c_42,c_43,c_45,c_46,c_47,c_49,c_50,c_51,c_52,c_53,c_2010,c_2076,c_2648])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_487,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X2_51,X3_51)
    | ~ m1_pre_topc(X0_51,X3_51)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | m1_subset_1(k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(X3_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X3_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X3_51)
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1066,plain,
    ( v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_pre_topc(X3_51,X2_51) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51)))) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_5029,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5027,c_1066])).

cnf(c_4129,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4118,c_1073])).

cnf(c_478,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1075,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_4130,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4118,c_1075])).

cnf(c_477,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1076,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_4132,plain,
    ( v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4118,c_1076])).

cnf(c_7385,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5029,c_38,c_39,c_40,c_41,c_42,c_45,c_46,c_49,c_2010,c_2076,c_2648,c_4129,c_4130,c_4132])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_492,plain,
    ( ~ r2_funct_2(X0_50,X1_50,X0_49,X1_49)
    | ~ v1_funct_2(X1_49,X0_50,X1_50)
    | ~ v1_funct_2(X0_49,X0_50,X1_50)
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(X1_49)
    | X0_49 = X1_49 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1061,plain,
    ( X0_49 = X1_49
    | r2_funct_2(X0_50,X1_50,X0_49,X1_49) != iProver_top
    | v1_funct_2(X0_49,X0_50,X1_50) != iProver_top
    | v1_funct_2(X1_49,X0_50,X1_50) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_7392,plain,
    ( k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = X0_49
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),X0_49) != iProver_top
    | v1_funct_2(X0_49,u1_struct_0(sK4),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7385,c_1061])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_486,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | v1_funct_2(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_49),u1_struct_0(X3_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_pre_topc(X0_51,X2_51)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X2_51)
    | v2_struct_0(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1067,plain,
    ( v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_49),u1_struct_0(X3_51),u1_struct_0(X1_51)) = iProver_top
    | m1_pre_topc(X3_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_5030,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5027,c_1067])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_485,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X2_51,X3_51)
    | ~ m1_pre_topc(X0_51,X3_51)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(X3_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X3_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X3_51)
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_49)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1068,plain,
    ( v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_pre_topc(X3_51,X2_51) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_2202,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))) = iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1073,c_1068])).

cnf(c_3801,plain,
    ( v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2202,c_40,c_41,c_42,c_54,c_55])).

cnf(c_3802,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3801])).

cnf(c_4124,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,k2_tmap_1(sK3,sK1,sK5,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4118,c_3802])).

cnf(c_5032,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5027,c_4124])).

cnf(c_7526,plain,
    ( v1_funct_1(X0_49) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = X0_49
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),X0_49) != iProver_top
    | v1_funct_2(X0_49,u1_struct_0(sK4),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7392,c_38,c_39,c_40,c_41,c_42,c_45,c_46,c_49,c_2010,c_2076,c_2648,c_4129,c_4130,c_4132,c_5030,c_5032])).

cnf(c_7527,plain,
    ( k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = X0_49
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),X0_49) != iProver_top
    | v1_funct_2(X0_49,u1_struct_0(sK4),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_7526])).

cnf(c_7748,plain,
    ( k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k2_tmap_1(sK3,sK1,sK5,sK4)
    | v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7744,c_7527])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_48,plain,
    ( m1_pre_topc(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_471,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1082,plain,
    ( m1_pre_topc(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_471])).

cnf(c_3413,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK3,sK4,sK5)
    | m1_pre_topc(sK4,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1082,c_3406])).

cnf(c_3176,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK3,sK1,sK5,sK4) ),
    inference(superposition,[status(thm)],[c_2648,c_3170])).

cnf(c_3419,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k2_tmap_1(sK3,sK1,sK5,sK4)
    | m1_pre_topc(sK4,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3413,c_3176])).

cnf(c_4744,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k2_tmap_1(sK3,sK1,sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3419,c_37,c_38,c_39,c_46,c_2648])).

cnf(c_4749,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4744,c_1066])).

cnf(c_4750,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4744,c_1067])).

cnf(c_2203,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(sK3,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_51,sK1,sK3,X0_51,sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1077,c_1068])).

cnf(c_3194,plain,
    ( v1_funct_1(k3_tmap_1(X1_51,sK1,sK3,X0_51,sK5)) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(sK3,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2203,c_40,c_41,c_42,c_51,c_52])).

cnf(c_3195,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(sK3,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_51,sK1,sK3,X0_51,sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3194])).

cnf(c_4751,plain,
    ( m1_pre_topc(sK4,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4744,c_3195])).

cnf(c_18264,plain,
    ( k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k2_tmap_1(sK3,sK1,sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7748,c_37,c_38,c_39,c_40,c_41,c_42,c_46,c_48,c_51,c_52,c_53,c_4749,c_4750,c_4751])).

cnf(c_12,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(k3_tmap_1(X3,X2,X1,X4,X0),X4,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_482,plain,
    ( ~ v5_pre_topc(X0_49,X0_51,X1_51)
    | v5_pre_topc(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_49),X3_51,X1_51)
    | ~ v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_pre_topc(X0_51,X2_51)
    | ~ m1_pre_topc(X3_51,X0_51)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X2_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X3_51)
    | v2_struct_0(X0_51)
    | ~ l1_pre_topc(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1071,plain,
    ( v5_pre_topc(X0_49,X0_51,X1_51) != iProver_top
    | v5_pre_topc(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_49),X3_51,X1_51) = iProver_top
    | v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X3_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_pre_topc(X3_51,X0_51) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(X3_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_482])).

cnf(c_5028,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),sK4,sK1) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK2),sK2,sK1) != iProver_top
    | v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5027,c_1071])).

cnf(c_17,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_479,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1074,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_4131,plain,
    ( v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK2),sK2,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4118,c_1074])).

cnf(c_7751,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),sK4,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5028,c_38,c_39,c_40,c_41,c_42,c_43,c_45,c_46,c_47,c_49,c_50,c_2010,c_2076,c_2648,c_4129,c_4130,c_4131,c_4132])).

cnf(c_18273,plain,
    ( v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18264,c_7751])).

cnf(c_15,negated_conjecture,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_481,negated_conjecture,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1072,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_58,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1200,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(X2_51,X1_51)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
    | v2_struct_0(X1_51)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k3_tmap_1(X1_51,sK1,X0_51,X2_51,X0_49)) ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_1443,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_51,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0_51,X0_49)) ),
    inference(instantiation,[status(thm)],[c_1200])).

cnf(c_1764,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,X0_49)) ),
    inference(instantiation,[status(thm)],[c_1443])).

cnf(c_1765,plain,
    ( v1_funct_2(X0_49,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1764])).

cnf(c_1767,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1765])).

cnf(c_1198,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(X2_51,X1_51)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
    | m1_subset_1(k3_tmap_1(X1_51,sK1,X0_51,X2_51,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(sK1))))
    | v2_struct_0(X1_51)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(X0_49) ),
    inference(instantiation,[status(thm)],[c_487])).

cnf(c_1507,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_51,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0_51,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_1(X0_49) ),
    inference(instantiation,[status(thm)],[c_1198])).

cnf(c_1858,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_1(X0_49) ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_1859,plain,
    ( v1_funct_2(X0_49,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1858])).

cnf(c_1861,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1859])).

cnf(c_1155,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | v1_funct_2(k3_tmap_1(sK0,X1_51,X0_51,X2_51,X0_49),u1_struct_0(X2_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X2_51,sK0)
    | ~ m1_pre_topc(X0_51,sK0)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_1(X0_49) ),
    inference(instantiation,[status(thm)],[c_486])).

cnf(c_1519,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | v1_funct_2(k3_tmap_1(sK0,X1_51,X0_51,sK4,X0_49),u1_struct_0(sK4),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X0_51,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_1(X0_49) ),
    inference(instantiation,[status(thm)],[c_1155])).

cnf(c_1919,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(sK3),u1_struct_0(X0_51))
    | v1_funct_2(k3_tmap_1(sK0,X0_51,sK3,sK4,X0_49),u1_struct_0(sK4),u1_struct_0(X0_51))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(X0_51)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_1(X0_49) ),
    inference(instantiation,[status(thm)],[c_1519])).

cnf(c_1920,plain,
    ( v1_funct_2(X0_49,u1_struct_0(sK3),u1_struct_0(X0_51)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,X0_51,sK3,sK4,X0_49),u1_struct_0(sK4),u1_struct_0(X0_51)) = iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1919])).

cnf(c_1922,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1920])).

cnf(c_2125,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1072,c_37,c_38,c_39,c_40,c_41,c_42,c_46,c_48,c_51,c_52,c_53,c_58,c_1767,c_1861,c_1922])).

cnf(c_4746,plain,
    ( v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4744,c_2125])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18273,c_4746])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:52:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.56/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.56/1.98  
% 11.56/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.56/1.98  
% 11.56/1.98  ------  iProver source info
% 11.56/1.98  
% 11.56/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.56/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.56/1.98  git: non_committed_changes: false
% 11.56/1.98  git: last_make_outside_of_git: false
% 11.56/1.98  
% 11.56/1.98  ------ 
% 11.56/1.98  
% 11.56/1.98  ------ Input Options
% 11.56/1.98  
% 11.56/1.98  --out_options                           all
% 11.56/1.98  --tptp_safe_out                         true
% 11.56/1.98  --problem_path                          ""
% 11.56/1.98  --include_path                          ""
% 11.56/1.98  --clausifier                            res/vclausify_rel
% 11.56/1.98  --clausifier_options                    ""
% 11.56/1.98  --stdin                                 false
% 11.56/1.98  --stats_out                             all
% 11.56/1.98  
% 11.56/1.98  ------ General Options
% 11.56/1.98  
% 11.56/1.98  --fof                                   false
% 11.56/1.98  --time_out_real                         305.
% 11.56/1.98  --time_out_virtual                      -1.
% 11.56/1.98  --symbol_type_check                     false
% 11.56/1.98  --clausify_out                          false
% 11.56/1.98  --sig_cnt_out                           false
% 11.56/1.98  --trig_cnt_out                          false
% 11.56/1.98  --trig_cnt_out_tolerance                1.
% 11.56/1.98  --trig_cnt_out_sk_spl                   false
% 11.56/1.98  --abstr_cl_out                          false
% 11.56/1.98  
% 11.56/1.98  ------ Global Options
% 11.56/1.98  
% 11.56/1.98  --schedule                              default
% 11.56/1.98  --add_important_lit                     false
% 11.56/1.98  --prop_solver_per_cl                    1000
% 11.56/1.98  --min_unsat_core                        false
% 11.56/1.98  --soft_assumptions                      false
% 11.56/1.98  --soft_lemma_size                       3
% 11.56/1.98  --prop_impl_unit_size                   0
% 11.56/1.98  --prop_impl_unit                        []
% 11.56/1.98  --share_sel_clauses                     true
% 11.56/1.98  --reset_solvers                         false
% 11.56/1.98  --bc_imp_inh                            [conj_cone]
% 11.56/1.98  --conj_cone_tolerance                   3.
% 11.56/1.98  --extra_neg_conj                        none
% 11.56/1.98  --large_theory_mode                     true
% 11.56/1.98  --prolific_symb_bound                   200
% 11.56/1.98  --lt_threshold                          2000
% 11.56/1.98  --clause_weak_htbl                      true
% 11.56/1.98  --gc_record_bc_elim                     false
% 11.56/1.98  
% 11.56/1.98  ------ Preprocessing Options
% 11.56/1.98  
% 11.56/1.98  --preprocessing_flag                    true
% 11.56/1.98  --time_out_prep_mult                    0.1
% 11.56/1.98  --splitting_mode                        input
% 11.56/1.98  --splitting_grd                         true
% 11.56/1.98  --splitting_cvd                         false
% 11.56/1.98  --splitting_cvd_svl                     false
% 11.56/1.98  --splitting_nvd                         32
% 11.56/1.98  --sub_typing                            true
% 11.56/1.98  --prep_gs_sim                           true
% 11.56/1.98  --prep_unflatten                        true
% 11.56/1.98  --prep_res_sim                          true
% 11.56/1.98  --prep_upred                            true
% 11.56/1.98  --prep_sem_filter                       exhaustive
% 11.56/1.98  --prep_sem_filter_out                   false
% 11.56/1.98  --pred_elim                             true
% 11.56/1.98  --res_sim_input                         true
% 11.56/1.98  --eq_ax_congr_red                       true
% 11.56/1.98  --pure_diseq_elim                       true
% 11.56/1.98  --brand_transform                       false
% 11.56/1.98  --non_eq_to_eq                          false
% 11.56/1.98  --prep_def_merge                        true
% 11.56/1.98  --prep_def_merge_prop_impl              false
% 11.56/1.98  --prep_def_merge_mbd                    true
% 11.56/1.98  --prep_def_merge_tr_red                 false
% 11.56/1.98  --prep_def_merge_tr_cl                  false
% 11.56/1.98  --smt_preprocessing                     true
% 11.56/1.98  --smt_ac_axioms                         fast
% 11.56/1.98  --preprocessed_out                      false
% 11.56/1.98  --preprocessed_stats                    false
% 11.56/1.98  
% 11.56/1.98  ------ Abstraction refinement Options
% 11.56/1.98  
% 11.56/1.98  --abstr_ref                             []
% 11.56/1.98  --abstr_ref_prep                        false
% 11.56/1.98  --abstr_ref_until_sat                   false
% 11.56/1.98  --abstr_ref_sig_restrict                funpre
% 11.56/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.56/1.98  --abstr_ref_under                       []
% 11.56/1.98  
% 11.56/1.98  ------ SAT Options
% 11.56/1.98  
% 11.56/1.98  --sat_mode                              false
% 11.56/1.98  --sat_fm_restart_options                ""
% 11.56/1.98  --sat_gr_def                            false
% 11.56/1.98  --sat_epr_types                         true
% 11.56/1.98  --sat_non_cyclic_types                  false
% 11.56/1.98  --sat_finite_models                     false
% 11.56/1.98  --sat_fm_lemmas                         false
% 11.56/1.98  --sat_fm_prep                           false
% 11.56/1.98  --sat_fm_uc_incr                        true
% 11.56/1.98  --sat_out_model                         small
% 11.56/1.98  --sat_out_clauses                       false
% 11.56/1.98  
% 11.56/1.98  ------ QBF Options
% 11.56/1.98  
% 11.56/1.98  --qbf_mode                              false
% 11.56/1.98  --qbf_elim_univ                         false
% 11.56/1.98  --qbf_dom_inst                          none
% 11.56/1.98  --qbf_dom_pre_inst                      false
% 11.56/1.98  --qbf_sk_in                             false
% 11.56/1.98  --qbf_pred_elim                         true
% 11.56/1.98  --qbf_split                             512
% 11.56/1.98  
% 11.56/1.98  ------ BMC1 Options
% 11.56/1.98  
% 11.56/1.98  --bmc1_incremental                      false
% 11.56/1.98  --bmc1_axioms                           reachable_all
% 11.56/1.98  --bmc1_min_bound                        0
% 11.56/1.98  --bmc1_max_bound                        -1
% 11.56/1.98  --bmc1_max_bound_default                -1
% 11.56/1.98  --bmc1_symbol_reachability              true
% 11.56/1.98  --bmc1_property_lemmas                  false
% 11.56/1.98  --bmc1_k_induction                      false
% 11.56/1.98  --bmc1_non_equiv_states                 false
% 11.56/1.98  --bmc1_deadlock                         false
% 11.56/1.98  --bmc1_ucm                              false
% 11.56/1.98  --bmc1_add_unsat_core                   none
% 11.56/1.98  --bmc1_unsat_core_children              false
% 11.56/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.56/1.98  --bmc1_out_stat                         full
% 11.56/1.98  --bmc1_ground_init                      false
% 11.56/1.98  --bmc1_pre_inst_next_state              false
% 11.56/1.98  --bmc1_pre_inst_state                   false
% 11.56/1.98  --bmc1_pre_inst_reach_state             false
% 11.56/1.98  --bmc1_out_unsat_core                   false
% 11.56/1.98  --bmc1_aig_witness_out                  false
% 11.56/1.98  --bmc1_verbose                          false
% 11.56/1.98  --bmc1_dump_clauses_tptp                false
% 11.56/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.56/1.98  --bmc1_dump_file                        -
% 11.56/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.56/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.56/1.98  --bmc1_ucm_extend_mode                  1
% 11.56/1.98  --bmc1_ucm_init_mode                    2
% 11.56/1.98  --bmc1_ucm_cone_mode                    none
% 11.56/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.56/1.98  --bmc1_ucm_relax_model                  4
% 11.56/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.56/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.56/1.98  --bmc1_ucm_layered_model                none
% 11.56/1.98  --bmc1_ucm_max_lemma_size               10
% 11.56/1.98  
% 11.56/1.98  ------ AIG Options
% 11.56/1.98  
% 11.56/1.98  --aig_mode                              false
% 11.56/1.98  
% 11.56/1.98  ------ Instantiation Options
% 11.56/1.98  
% 11.56/1.98  --instantiation_flag                    true
% 11.56/1.98  --inst_sos_flag                         true
% 11.56/1.98  --inst_sos_phase                        true
% 11.56/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.56/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.56/1.98  --inst_lit_sel_side                     num_symb
% 11.56/1.98  --inst_solver_per_active                1400
% 11.56/1.98  --inst_solver_calls_frac                1.
% 11.56/1.98  --inst_passive_queue_type               priority_queues
% 11.56/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.56/1.98  --inst_passive_queues_freq              [25;2]
% 11.56/1.98  --inst_dismatching                      true
% 11.56/1.98  --inst_eager_unprocessed_to_passive     true
% 11.56/1.98  --inst_prop_sim_given                   true
% 11.56/1.98  --inst_prop_sim_new                     false
% 11.56/1.98  --inst_subs_new                         false
% 11.56/1.98  --inst_eq_res_simp                      false
% 11.56/1.98  --inst_subs_given                       false
% 11.56/1.98  --inst_orphan_elimination               true
% 11.56/1.98  --inst_learning_loop_flag               true
% 11.56/1.98  --inst_learning_start                   3000
% 11.56/1.98  --inst_learning_factor                  2
% 11.56/1.98  --inst_start_prop_sim_after_learn       3
% 11.56/1.98  --inst_sel_renew                        solver
% 11.56/1.98  --inst_lit_activity_flag                true
% 11.56/1.98  --inst_restr_to_given                   false
% 11.56/1.98  --inst_activity_threshold               500
% 11.56/1.98  --inst_out_proof                        true
% 11.56/1.98  
% 11.56/1.98  ------ Resolution Options
% 11.56/1.98  
% 11.56/1.98  --resolution_flag                       true
% 11.56/1.98  --res_lit_sel                           adaptive
% 11.56/1.98  --res_lit_sel_side                      none
% 11.56/1.98  --res_ordering                          kbo
% 11.56/1.98  --res_to_prop_solver                    active
% 11.56/1.98  --res_prop_simpl_new                    false
% 11.56/1.98  --res_prop_simpl_given                  true
% 11.56/1.98  --res_passive_queue_type                priority_queues
% 11.56/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.56/1.98  --res_passive_queues_freq               [15;5]
% 11.56/1.98  --res_forward_subs                      full
% 11.56/1.98  --res_backward_subs                     full
% 11.56/1.98  --res_forward_subs_resolution           true
% 11.56/1.98  --res_backward_subs_resolution          true
% 11.56/1.98  --res_orphan_elimination                true
% 11.56/1.98  --res_time_limit                        2.
% 11.56/1.98  --res_out_proof                         true
% 11.56/1.98  
% 11.56/1.98  ------ Superposition Options
% 11.56/1.98  
% 11.56/1.98  --superposition_flag                    true
% 11.56/1.98  --sup_passive_queue_type                priority_queues
% 11.56/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.56/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.56/1.98  --demod_completeness_check              fast
% 11.56/1.98  --demod_use_ground                      true
% 11.56/1.98  --sup_to_prop_solver                    passive
% 11.56/1.98  --sup_prop_simpl_new                    true
% 11.56/1.98  --sup_prop_simpl_given                  true
% 11.56/1.98  --sup_fun_splitting                     true
% 11.56/1.98  --sup_smt_interval                      50000
% 11.56/1.98  
% 11.56/1.98  ------ Superposition Simplification Setup
% 11.56/1.98  
% 11.56/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.56/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.56/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.56/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.56/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.56/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.56/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.56/1.98  --sup_immed_triv                        [TrivRules]
% 11.56/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.56/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.56/1.98  --sup_immed_bw_main                     []
% 11.56/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.56/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.56/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.56/1.98  --sup_input_bw                          []
% 11.56/1.98  
% 11.56/1.98  ------ Combination Options
% 11.56/1.98  
% 11.56/1.98  --comb_res_mult                         3
% 11.56/1.98  --comb_sup_mult                         2
% 11.56/1.98  --comb_inst_mult                        10
% 11.56/1.98  
% 11.56/1.98  ------ Debug Options
% 11.56/1.98  
% 11.56/1.98  --dbg_backtrace                         false
% 11.56/1.98  --dbg_dump_prop_clauses                 false
% 11.56/1.98  --dbg_dump_prop_clauses_file            -
% 11.56/1.98  --dbg_out_stat                          false
% 11.56/1.98  ------ Parsing...
% 11.56/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.56/1.98  
% 11.56/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.56/1.98  
% 11.56/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.56/1.98  
% 11.56/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.56/1.98  ------ Proving...
% 11.56/1.98  ------ Problem Properties 
% 11.56/1.98  
% 11.56/1.98  
% 11.56/1.98  clauses                                 37
% 11.56/1.98  conjectures                             22
% 11.56/1.98  EPR                                     18
% 11.56/1.98  Horn                                    27
% 11.56/1.98  unary                                   21
% 11.56/1.98  binary                                  0
% 11.56/1.98  lits                                    176
% 11.56/1.98  lits eq                                 3
% 11.56/1.98  fd_pure                                 0
% 11.56/1.98  fd_pseudo                               0
% 11.56/1.98  fd_cond                                 0
% 11.56/1.98  fd_pseudo_cond                          1
% 11.56/1.98  AC symbols                              0
% 11.56/1.98  
% 11.56/1.98  ------ Schedule dynamic 5 is on 
% 11.56/1.98  
% 11.56/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.56/1.98  
% 11.56/1.98  
% 11.56/1.98  ------ 
% 11.56/1.98  Current options:
% 11.56/1.98  ------ 
% 11.56/1.98  
% 11.56/1.98  ------ Input Options
% 11.56/1.98  
% 11.56/1.98  --out_options                           all
% 11.56/1.98  --tptp_safe_out                         true
% 11.56/1.98  --problem_path                          ""
% 11.56/1.98  --include_path                          ""
% 11.56/1.98  --clausifier                            res/vclausify_rel
% 11.56/1.98  --clausifier_options                    ""
% 11.56/1.98  --stdin                                 false
% 11.56/1.98  --stats_out                             all
% 11.56/1.98  
% 11.56/1.98  ------ General Options
% 11.56/1.98  
% 11.56/1.98  --fof                                   false
% 11.56/1.98  --time_out_real                         305.
% 11.56/1.98  --time_out_virtual                      -1.
% 11.56/1.98  --symbol_type_check                     false
% 11.56/1.98  --clausify_out                          false
% 11.56/1.98  --sig_cnt_out                           false
% 11.56/1.98  --trig_cnt_out                          false
% 11.56/1.98  --trig_cnt_out_tolerance                1.
% 11.56/1.98  --trig_cnt_out_sk_spl                   false
% 11.56/1.98  --abstr_cl_out                          false
% 11.56/1.98  
% 11.56/1.98  ------ Global Options
% 11.56/1.98  
% 11.56/1.98  --schedule                              default
% 11.56/1.98  --add_important_lit                     false
% 11.56/1.98  --prop_solver_per_cl                    1000
% 11.56/1.98  --min_unsat_core                        false
% 11.56/1.98  --soft_assumptions                      false
% 11.56/1.98  --soft_lemma_size                       3
% 11.56/1.98  --prop_impl_unit_size                   0
% 11.56/1.98  --prop_impl_unit                        []
% 11.56/1.98  --share_sel_clauses                     true
% 11.56/1.98  --reset_solvers                         false
% 11.56/1.98  --bc_imp_inh                            [conj_cone]
% 11.56/1.98  --conj_cone_tolerance                   3.
% 11.56/1.98  --extra_neg_conj                        none
% 11.56/1.98  --large_theory_mode                     true
% 11.56/1.98  --prolific_symb_bound                   200
% 11.56/1.98  --lt_threshold                          2000
% 11.56/1.98  --clause_weak_htbl                      true
% 11.56/1.98  --gc_record_bc_elim                     false
% 11.56/1.98  
% 11.56/1.98  ------ Preprocessing Options
% 11.56/1.98  
% 11.56/1.98  --preprocessing_flag                    true
% 11.56/1.98  --time_out_prep_mult                    0.1
% 11.56/1.98  --splitting_mode                        input
% 11.56/1.98  --splitting_grd                         true
% 11.56/1.98  --splitting_cvd                         false
% 11.56/1.98  --splitting_cvd_svl                     false
% 11.56/1.98  --splitting_nvd                         32
% 11.56/1.98  --sub_typing                            true
% 11.56/1.98  --prep_gs_sim                           true
% 11.56/1.98  --prep_unflatten                        true
% 11.56/1.98  --prep_res_sim                          true
% 11.56/1.98  --prep_upred                            true
% 11.56/1.98  --prep_sem_filter                       exhaustive
% 11.56/1.98  --prep_sem_filter_out                   false
% 11.56/1.98  --pred_elim                             true
% 11.56/1.98  --res_sim_input                         true
% 11.56/1.98  --eq_ax_congr_red                       true
% 11.56/1.98  --pure_diseq_elim                       true
% 11.56/1.98  --brand_transform                       false
% 11.56/1.98  --non_eq_to_eq                          false
% 11.56/1.98  --prep_def_merge                        true
% 11.56/1.98  --prep_def_merge_prop_impl              false
% 11.56/1.98  --prep_def_merge_mbd                    true
% 11.56/1.98  --prep_def_merge_tr_red                 false
% 11.56/1.98  --prep_def_merge_tr_cl                  false
% 11.56/1.98  --smt_preprocessing                     true
% 11.56/1.98  --smt_ac_axioms                         fast
% 11.56/1.98  --preprocessed_out                      false
% 11.56/1.98  --preprocessed_stats                    false
% 11.56/1.98  
% 11.56/1.98  ------ Abstraction refinement Options
% 11.56/1.98  
% 11.56/1.98  --abstr_ref                             []
% 11.56/1.98  --abstr_ref_prep                        false
% 11.56/1.98  --abstr_ref_until_sat                   false
% 11.56/1.98  --abstr_ref_sig_restrict                funpre
% 11.56/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.56/1.98  --abstr_ref_under                       []
% 11.56/1.98  
% 11.56/1.98  ------ SAT Options
% 11.56/1.98  
% 11.56/1.98  --sat_mode                              false
% 11.56/1.98  --sat_fm_restart_options                ""
% 11.56/1.98  --sat_gr_def                            false
% 11.56/1.98  --sat_epr_types                         true
% 11.56/1.98  --sat_non_cyclic_types                  false
% 11.56/1.98  --sat_finite_models                     false
% 11.56/1.98  --sat_fm_lemmas                         false
% 11.56/1.98  --sat_fm_prep                           false
% 11.56/1.98  --sat_fm_uc_incr                        true
% 11.56/1.98  --sat_out_model                         small
% 11.56/1.98  --sat_out_clauses                       false
% 11.56/1.98  
% 11.56/1.98  ------ QBF Options
% 11.56/1.98  
% 11.56/1.98  --qbf_mode                              false
% 11.56/1.98  --qbf_elim_univ                         false
% 11.56/1.98  --qbf_dom_inst                          none
% 11.56/1.98  --qbf_dom_pre_inst                      false
% 11.56/1.98  --qbf_sk_in                             false
% 11.56/1.98  --qbf_pred_elim                         true
% 11.56/1.98  --qbf_split                             512
% 11.56/1.98  
% 11.56/1.98  ------ BMC1 Options
% 11.56/1.98  
% 11.56/1.98  --bmc1_incremental                      false
% 11.56/1.98  --bmc1_axioms                           reachable_all
% 11.56/1.98  --bmc1_min_bound                        0
% 11.56/1.98  --bmc1_max_bound                        -1
% 11.56/1.98  --bmc1_max_bound_default                -1
% 11.56/1.98  --bmc1_symbol_reachability              true
% 11.56/1.98  --bmc1_property_lemmas                  false
% 11.56/1.98  --bmc1_k_induction                      false
% 11.56/1.98  --bmc1_non_equiv_states                 false
% 11.56/1.98  --bmc1_deadlock                         false
% 11.56/1.98  --bmc1_ucm                              false
% 11.56/1.98  --bmc1_add_unsat_core                   none
% 11.56/1.98  --bmc1_unsat_core_children              false
% 11.56/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.56/1.98  --bmc1_out_stat                         full
% 11.56/1.98  --bmc1_ground_init                      false
% 11.56/1.98  --bmc1_pre_inst_next_state              false
% 11.56/1.98  --bmc1_pre_inst_state                   false
% 11.56/1.98  --bmc1_pre_inst_reach_state             false
% 11.56/1.98  --bmc1_out_unsat_core                   false
% 11.56/1.98  --bmc1_aig_witness_out                  false
% 11.56/1.98  --bmc1_verbose                          false
% 11.56/1.98  --bmc1_dump_clauses_tptp                false
% 11.56/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.56/1.98  --bmc1_dump_file                        -
% 11.56/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.56/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.56/1.98  --bmc1_ucm_extend_mode                  1
% 11.56/1.98  --bmc1_ucm_init_mode                    2
% 11.56/1.98  --bmc1_ucm_cone_mode                    none
% 11.56/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.56/1.98  --bmc1_ucm_relax_model                  4
% 11.56/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.56/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.56/1.98  --bmc1_ucm_layered_model                none
% 11.56/1.98  --bmc1_ucm_max_lemma_size               10
% 11.56/1.98  
% 11.56/1.98  ------ AIG Options
% 11.56/1.98  
% 11.56/1.98  --aig_mode                              false
% 11.56/1.98  
% 11.56/1.98  ------ Instantiation Options
% 11.56/1.98  
% 11.56/1.98  --instantiation_flag                    true
% 11.56/1.98  --inst_sos_flag                         true
% 11.56/1.98  --inst_sos_phase                        true
% 11.56/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.56/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.56/1.98  --inst_lit_sel_side                     none
% 11.56/1.98  --inst_solver_per_active                1400
% 11.56/1.98  --inst_solver_calls_frac                1.
% 11.56/1.98  --inst_passive_queue_type               priority_queues
% 11.56/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.56/1.98  --inst_passive_queues_freq              [25;2]
% 11.56/1.98  --inst_dismatching                      true
% 11.56/1.98  --inst_eager_unprocessed_to_passive     true
% 11.56/1.98  --inst_prop_sim_given                   true
% 11.56/1.98  --inst_prop_sim_new                     false
% 11.56/1.98  --inst_subs_new                         false
% 11.56/1.98  --inst_eq_res_simp                      false
% 11.56/1.98  --inst_subs_given                       false
% 11.56/1.98  --inst_orphan_elimination               true
% 11.56/1.98  --inst_learning_loop_flag               true
% 11.56/1.98  --inst_learning_start                   3000
% 11.56/1.98  --inst_learning_factor                  2
% 11.56/1.98  --inst_start_prop_sim_after_learn       3
% 11.56/1.98  --inst_sel_renew                        solver
% 11.56/1.98  --inst_lit_activity_flag                true
% 11.56/1.98  --inst_restr_to_given                   false
% 11.56/1.98  --inst_activity_threshold               500
% 11.56/1.98  --inst_out_proof                        true
% 11.56/1.98  
% 11.56/1.98  ------ Resolution Options
% 11.56/1.98  
% 11.56/1.98  --resolution_flag                       false
% 11.56/1.98  --res_lit_sel                           adaptive
% 11.56/1.98  --res_lit_sel_side                      none
% 11.56/1.98  --res_ordering                          kbo
% 11.56/1.98  --res_to_prop_solver                    active
% 11.56/1.98  --res_prop_simpl_new                    false
% 11.56/1.98  --res_prop_simpl_given                  true
% 11.56/1.98  --res_passive_queue_type                priority_queues
% 11.56/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.56/1.98  --res_passive_queues_freq               [15;5]
% 11.56/1.98  --res_forward_subs                      full
% 11.56/1.98  --res_backward_subs                     full
% 11.56/1.98  --res_forward_subs_resolution           true
% 11.56/1.98  --res_backward_subs_resolution          true
% 11.56/1.98  --res_orphan_elimination                true
% 11.56/1.98  --res_time_limit                        2.
% 11.56/1.98  --res_out_proof                         true
% 11.56/1.98  
% 11.56/1.98  ------ Superposition Options
% 11.56/1.98  
% 11.56/1.98  --superposition_flag                    true
% 11.56/1.98  --sup_passive_queue_type                priority_queues
% 11.56/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.56/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.56/1.98  --demod_completeness_check              fast
% 11.56/1.98  --demod_use_ground                      true
% 11.56/1.98  --sup_to_prop_solver                    passive
% 11.56/1.98  --sup_prop_simpl_new                    true
% 11.56/1.98  --sup_prop_simpl_given                  true
% 11.56/1.98  --sup_fun_splitting                     true
% 11.56/1.98  --sup_smt_interval                      50000
% 11.56/1.98  
% 11.56/1.98  ------ Superposition Simplification Setup
% 11.56/1.98  
% 11.56/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.56/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.56/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.56/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.56/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.56/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.56/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.56/1.98  --sup_immed_triv                        [TrivRules]
% 11.56/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.56/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.56/1.98  --sup_immed_bw_main                     []
% 11.56/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.56/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.56/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.56/1.98  --sup_input_bw                          []
% 11.56/1.98  
% 11.56/1.98  ------ Combination Options
% 11.56/1.98  
% 11.56/1.98  --comb_res_mult                         3
% 11.56/1.98  --comb_sup_mult                         2
% 11.56/1.98  --comb_inst_mult                        10
% 11.56/1.98  
% 11.56/1.98  ------ Debug Options
% 11.56/1.98  
% 11.56/1.98  --dbg_backtrace                         false
% 11.56/1.98  --dbg_dump_prop_clauses                 false
% 11.56/1.98  --dbg_dump_prop_clauses_file            -
% 11.56/1.98  --dbg_out_stat                          false
% 11.56/1.98  
% 11.56/1.98  
% 11.56/1.98  
% 11.56/1.98  
% 11.56/1.98  ------ Proving...
% 11.56/1.98  
% 11.56/1.98  
% 11.56/1.98  % SZS status Theorem for theBenchmark.p
% 11.56/1.98  
% 11.56/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.56/1.98  
% 11.56/1.98  fof(f10,conjecture,(
% 11.56/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))) => (m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)))))))))))),
% 11.56/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.56/1.98  
% 11.56/1.98  fof(f11,negated_conjecture,(
% 11.56/1.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))) => (m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)))))))))))),
% 11.56/1.98    inference(negated_conjecture,[],[f10])).
% 11.56/1.98  
% 11.56/1.98  fof(f29,plain,(
% 11.56/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & (m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3))) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 11.56/1.98    inference(ennf_transformation,[],[f11])).
% 11.56/1.98  
% 11.56/1.98  fof(f30,plain,(
% 11.56/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.56/1.98    inference(flattening,[],[f29])).
% 11.56/1.98  
% 11.56/1.98  fof(f37,plain,(
% 11.56/1.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,sK5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,sK5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,sK5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,sK5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,sK5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 11.56/1.98    introduced(choice_axiom,[])).
% 11.56/1.98  
% 11.56/1.98  fof(f36,plain,(
% 11.56/1.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,sK4,X5),sK4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,sK4,X5),u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,sK4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(sK4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 11.56/1.98    introduced(choice_axiom,[])).
% 11.56/1.98  
% 11.56/1.98  fof(f35,plain,(
% 11.56/1.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,sK3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,sK3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,sK3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,sK3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,sK3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,sK3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,sK3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,sK3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 11.56/1.98    introduced(choice_axiom,[])).
% 11.56/1.98  
% 11.56/1.98  fof(f34,plain,(
% 11.56/1.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,sK2,X5),sK2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,sK2,X5),u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,sK2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK2) & m1_pre_topc(sK2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 11.56/1.98    introduced(choice_axiom,[])).
% 11.56/1.98  
% 11.56/1.98  fof(f33,plain,(
% 11.56/1.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(X0,sK1,X3,X4,X5),X4,sK1) | ~v1_funct_2(k3_tmap_1(X0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(X0,sK1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,sK1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(X0,sK1,X3,X2,X5),X2,sK1) & v1_funct_2(k3_tmap_1(X0,sK1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(X0,sK1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 11.56/1.98    introduced(choice_axiom,[])).
% 11.56/1.98  
% 11.56/1.98  fof(f32,plain,(
% 11.56/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(sK0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(sK0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 11.56/1.98    introduced(choice_axiom,[])).
% 11.56/1.98  
% 11.56/1.98  fof(f38,plain,(
% 11.56/1.98    ((((((~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))) & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 11.56/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f30,f37,f36,f35,f34,f33,f32])).
% 11.56/1.98  
% 11.56/1.98  fof(f67,plain,(
% 11.56/1.98    m1_pre_topc(sK4,sK2)),
% 11.56/1.98    inference(cnf_transformation,[],[f38])).
% 11.56/1.98  
% 11.56/1.98  fof(f66,plain,(
% 11.56/1.98    m1_pre_topc(sK2,sK3)),
% 11.56/1.98    inference(cnf_transformation,[],[f38])).
% 11.56/1.98  
% 11.56/1.98  fof(f8,axiom,(
% 11.56/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 11.56/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.56/1.98  
% 11.56/1.98  fof(f25,plain,(
% 11.56/1.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.56/1.98    inference(ennf_transformation,[],[f8])).
% 11.56/1.98  
% 11.56/1.98  fof(f26,plain,(
% 11.56/1.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.56/1.98    inference(flattening,[],[f25])).
% 11.56/1.98  
% 11.56/1.98  fof(f49,plain,(
% 11.56/1.98    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.56/1.98    inference(cnf_transformation,[],[f26])).
% 11.56/1.98  
% 11.56/1.98  fof(f55,plain,(
% 11.56/1.98    v2_pre_topc(sK0)),
% 11.56/1.98    inference(cnf_transformation,[],[f38])).
% 11.56/1.98  
% 11.56/1.98  fof(f56,plain,(
% 11.56/1.98    l1_pre_topc(sK0)),
% 11.56/1.98    inference(cnf_transformation,[],[f38])).
% 11.56/1.98  
% 11.56/1.98  fof(f63,plain,(
% 11.56/1.98    m1_pre_topc(sK3,sK0)),
% 11.56/1.98    inference(cnf_transformation,[],[f38])).
% 11.56/1.98  
% 11.56/1.98  fof(f3,axiom,(
% 11.56/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 11.56/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.56/1.98  
% 11.56/1.98  fof(f16,plain,(
% 11.56/1.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.56/1.98    inference(ennf_transformation,[],[f3])).
% 11.56/1.98  
% 11.56/1.98  fof(f42,plain,(
% 11.56/1.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.56/1.98    inference(cnf_transformation,[],[f16])).
% 11.56/1.98  
% 11.56/1.98  fof(f2,axiom,(
% 11.56/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 11.56/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.56/1.98  
% 11.56/1.98  fof(f14,plain,(
% 11.56/1.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.56/1.98    inference(ennf_transformation,[],[f2])).
% 11.56/1.98  
% 11.56/1.98  fof(f15,plain,(
% 11.56/1.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.56/1.98    inference(flattening,[],[f14])).
% 11.56/1.98  
% 11.56/1.98  fof(f41,plain,(
% 11.56/1.98    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.56/1.98    inference(cnf_transformation,[],[f15])).
% 11.56/1.98  
% 11.56/1.98  fof(f74,plain,(
% 11.56/1.98    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 11.56/1.98    inference(cnf_transformation,[],[f38])).
% 11.56/1.98  
% 11.56/1.98  fof(f5,axiom,(
% 11.56/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 11.56/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.56/1.98  
% 11.56/1.98  fof(f19,plain,(
% 11.56/1.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.56/1.98    inference(ennf_transformation,[],[f5])).
% 11.56/1.98  
% 11.56/1.98  fof(f20,plain,(
% 11.56/1.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.56/1.98    inference(flattening,[],[f19])).
% 11.56/1.98  
% 11.56/1.98  fof(f44,plain,(
% 11.56/1.98    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.56/1.98    inference(cnf_transformation,[],[f20])).
% 11.56/1.98  
% 11.56/1.98  fof(f57,plain,(
% 11.56/1.98    ~v2_struct_0(sK1)),
% 11.56/1.98    inference(cnf_transformation,[],[f38])).
% 11.56/1.98  
% 11.56/1.98  fof(f58,plain,(
% 11.56/1.98    v2_pre_topc(sK1)),
% 11.56/1.98    inference(cnf_transformation,[],[f38])).
% 11.56/1.98  
% 11.56/1.98  fof(f59,plain,(
% 11.56/1.98    l1_pre_topc(sK1)),
% 11.56/1.98    inference(cnf_transformation,[],[f38])).
% 11.56/1.98  
% 11.56/1.98  fof(f71,plain,(
% 11.56/1.98    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))),
% 11.56/1.98    inference(cnf_transformation,[],[f38])).
% 11.56/1.98  
% 11.56/1.98  fof(f72,plain,(
% 11.56/1.98    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))),
% 11.56/1.98    inference(cnf_transformation,[],[f38])).
% 11.56/1.98  
% 11.56/1.98  fof(f4,axiom,(
% 11.56/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 11.56/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.56/1.98  
% 11.56/1.98  fof(f17,plain,(
% 11.56/1.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.56/1.98    inference(ennf_transformation,[],[f4])).
% 11.56/1.98  
% 11.56/1.98  fof(f18,plain,(
% 11.56/1.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.56/1.98    inference(flattening,[],[f17])).
% 11.56/1.98  
% 11.56/1.98  fof(f43,plain,(
% 11.56/1.98    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.56/1.98    inference(cnf_transformation,[],[f18])).
% 11.56/1.98  
% 11.56/1.98  fof(f60,plain,(
% 11.56/1.98    ~v2_struct_0(sK2)),
% 11.56/1.98    inference(cnf_transformation,[],[f38])).
% 11.56/1.98  
% 11.56/1.98  fof(f61,plain,(
% 11.56/1.98    m1_pre_topc(sK2,sK0)),
% 11.56/1.98    inference(cnf_transformation,[],[f38])).
% 11.56/1.98  
% 11.56/1.98  fof(f62,plain,(
% 11.56/1.98    ~v2_struct_0(sK3)),
% 11.56/1.98    inference(cnf_transformation,[],[f38])).
% 11.56/1.98  
% 11.56/1.98  fof(f70,plain,(
% 11.56/1.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 11.56/1.98    inference(cnf_transformation,[],[f38])).
% 11.56/1.98  
% 11.56/1.98  fof(f68,plain,(
% 11.56/1.98    v1_funct_1(sK5)),
% 11.56/1.98    inference(cnf_transformation,[],[f38])).
% 11.56/1.98  
% 11.56/1.98  fof(f69,plain,(
% 11.56/1.98    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))),
% 11.56/1.98    inference(cnf_transformation,[],[f38])).
% 11.56/1.98  
% 11.56/1.98  fof(f54,plain,(
% 11.56/1.98    ~v2_struct_0(sK0)),
% 11.56/1.98    inference(cnf_transformation,[],[f38])).
% 11.56/1.98  
% 11.56/1.98  fof(f7,axiom,(
% 11.56/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 11.56/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.56/1.98  
% 11.56/1.98  fof(f23,plain,(
% 11.56/1.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.56/1.98    inference(ennf_transformation,[],[f7])).
% 11.56/1.98  
% 11.56/1.98  fof(f24,plain,(
% 11.56/1.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.56/1.98    inference(flattening,[],[f23])).
% 11.56/1.98  
% 11.56/1.98  fof(f48,plain,(
% 11.56/1.98    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.56/1.99    inference(cnf_transformation,[],[f24])).
% 11.56/1.99  
% 11.56/1.99  fof(f64,plain,(
% 11.56/1.99    ~v2_struct_0(sK4)),
% 11.56/1.99    inference(cnf_transformation,[],[f38])).
% 11.56/1.99  
% 11.56/1.99  fof(f6,axiom,(
% 11.56/1.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 11.56/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.56/1.99  
% 11.56/1.99  fof(f21,plain,(
% 11.56/1.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.56/1.99    inference(ennf_transformation,[],[f6])).
% 11.56/1.99  
% 11.56/1.99  fof(f22,plain,(
% 11.56/1.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.56/1.99    inference(flattening,[],[f21])).
% 11.56/1.99  
% 11.56/1.99  fof(f47,plain,(
% 11.56/1.99    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.56/1.99    inference(cnf_transformation,[],[f22])).
% 11.56/1.99  
% 11.56/1.99  fof(f1,axiom,(
% 11.56/1.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 11.56/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.56/1.99  
% 11.56/1.99  fof(f12,plain,(
% 11.56/1.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.56/1.99    inference(ennf_transformation,[],[f1])).
% 11.56/1.99  
% 11.56/1.99  fof(f13,plain,(
% 11.56/1.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.56/1.99    inference(flattening,[],[f12])).
% 11.56/1.99  
% 11.56/1.99  fof(f31,plain,(
% 11.56/1.99    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.56/1.99    inference(nnf_transformation,[],[f13])).
% 11.56/1.99  
% 11.56/1.99  fof(f39,plain,(
% 11.56/1.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.56/1.99    inference(cnf_transformation,[],[f31])).
% 11.56/1.99  
% 11.56/1.99  fof(f46,plain,(
% 11.56/1.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.56/1.99    inference(cnf_transformation,[],[f22])).
% 11.56/1.99  
% 11.56/1.99  fof(f45,plain,(
% 11.56/1.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.56/1.99    inference(cnf_transformation,[],[f22])).
% 11.56/1.99  
% 11.56/1.99  fof(f65,plain,(
% 11.56/1.99    m1_pre_topc(sK4,sK0)),
% 11.56/1.99    inference(cnf_transformation,[],[f38])).
% 11.56/1.99  
% 11.56/1.99  fof(f9,axiom,(
% 11.56/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)))))))))),
% 11.56/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.56/1.99  
% 11.56/1.99  fof(f27,plain,(
% 11.56/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.56/1.99    inference(ennf_transformation,[],[f9])).
% 11.56/1.99  
% 11.56/1.99  fof(f28,plain,(
% 11.56/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.56/1.99    inference(flattening,[],[f27])).
% 11.56/1.99  
% 11.56/1.99  fof(f52,plain,(
% 11.56/1.99    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.56/1.99    inference(cnf_transformation,[],[f28])).
% 11.56/1.99  
% 11.56/1.99  fof(f73,plain,(
% 11.56/1.99    v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)),
% 11.56/1.99    inference(cnf_transformation,[],[f38])).
% 11.56/1.99  
% 11.56/1.99  fof(f75,plain,(
% 11.56/1.99    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))),
% 11.56/1.99    inference(cnf_transformation,[],[f38])).
% 11.56/1.99  
% 11.56/1.99  cnf(c_23,negated_conjecture,
% 11.56/1.99      ( m1_pre_topc(sK4,sK2) ),
% 11.56/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_473,negated_conjecture,
% 11.56/1.99      ( m1_pre_topc(sK4,sK2) ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_23]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1080,plain,
% 11.56/1.99      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_24,negated_conjecture,
% 11.56/1.99      ( m1_pre_topc(sK2,sK3) ),
% 11.56/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_472,negated_conjecture,
% 11.56/1.99      ( m1_pre_topc(sK2,sK3) ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_24]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1081,plain,
% 11.56/1.99      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_472]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_10,plain,
% 11.56/1.99      ( ~ m1_pre_topc(X0,X1)
% 11.56/1.99      | ~ m1_pre_topc(X2,X0)
% 11.56/1.99      | m1_pre_topc(X2,X1)
% 11.56/1.99      | ~ l1_pre_topc(X1)
% 11.56/1.99      | ~ v2_pre_topc(X1) ),
% 11.56/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_483,plain,
% 11.56/1.99      ( ~ m1_pre_topc(X0_51,X1_51)
% 11.56/1.99      | ~ m1_pre_topc(X2_51,X0_51)
% 11.56/1.99      | m1_pre_topc(X2_51,X1_51)
% 11.56/1.99      | ~ l1_pre_topc(X1_51)
% 11.56/1.99      | ~ v2_pre_topc(X1_51) ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_10]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1070,plain,
% 11.56/1.99      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(X2_51,X1_51) = iProver_top
% 11.56/1.99      | l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_2085,plain,
% 11.56/1.99      ( m1_pre_topc(X0_51,sK2) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,sK3) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK3) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK3) != iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_1081,c_1070]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_35,negated_conjecture,
% 11.56/1.99      ( v2_pre_topc(sK0) ),
% 11.56/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_38,plain,
% 11.56/1.99      ( v2_pre_topc(sK0) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_34,negated_conjecture,
% 11.56/1.99      ( l1_pre_topc(sK0) ),
% 11.56/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_39,plain,
% 11.56/1.99      ( l1_pre_topc(sK0) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_27,negated_conjecture,
% 11.56/1.99      ( m1_pre_topc(sK3,sK0) ),
% 11.56/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_46,plain,
% 11.56/1.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_49,plain,
% 11.56/1.99      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1674,plain,
% 11.56/1.99      ( ~ m1_pre_topc(X0_51,sK2)
% 11.56/1.99      | m1_pre_topc(X0_51,sK3)
% 11.56/1.99      | ~ m1_pre_topc(sK2,sK3)
% 11.56/1.99      | ~ l1_pre_topc(sK3)
% 11.56/1.99      | ~ v2_pre_topc(sK3) ),
% 11.56/1.99      inference(instantiation,[status(thm)],[c_483]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1675,plain,
% 11.56/1.99      ( m1_pre_topc(X0_51,sK2) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,sK3) = iProver_top
% 11.56/1.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 11.56/1.99      | l1_pre_topc(sK3) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK3) != iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_1674]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3,plain,
% 11.56/1.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 11.56/1.99      inference(cnf_transformation,[],[f42]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_490,plain,
% 11.56/1.99      ( ~ m1_pre_topc(X0_51,X1_51)
% 11.56/1.99      | ~ l1_pre_topc(X1_51)
% 11.56/1.99      | l1_pre_topc(X0_51) ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_3]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1459,plain,
% 11.56/1.99      ( ~ m1_pre_topc(sK3,X0_51)
% 11.56/1.99      | ~ l1_pre_topc(X0_51)
% 11.56/1.99      | l1_pre_topc(sK3) ),
% 11.56/1.99      inference(instantiation,[status(thm)],[c_490]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_2009,plain,
% 11.56/1.99      ( ~ m1_pre_topc(sK3,sK0) | l1_pre_topc(sK3) | ~ l1_pre_topc(sK0) ),
% 11.56/1.99      inference(instantiation,[status(thm)],[c_1459]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_2010,plain,
% 11.56/1.99      ( m1_pre_topc(sK3,sK0) != iProver_top
% 11.56/1.99      | l1_pre_topc(sK3) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_2009]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_469,negated_conjecture,
% 11.56/1.99      ( m1_pre_topc(sK3,sK0) ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_27]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1084,plain,
% 11.56/1.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_469]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_2,plain,
% 11.56/1.99      ( ~ m1_pre_topc(X0,X1)
% 11.56/1.99      | ~ l1_pre_topc(X1)
% 11.56/1.99      | ~ v2_pre_topc(X1)
% 11.56/1.99      | v2_pre_topc(X0) ),
% 11.56/1.99      inference(cnf_transformation,[],[f41]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_491,plain,
% 11.56/1.99      ( ~ m1_pre_topc(X0_51,X1_51)
% 11.56/1.99      | ~ l1_pre_topc(X1_51)
% 11.56/1.99      | ~ v2_pre_topc(X1_51)
% 11.56/1.99      | v2_pre_topc(X0_51) ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_2]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1062,plain,
% 11.56/1.99      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.56/1.99      | l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X0_51) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_2076,plain,
% 11.56/1.99      ( l1_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK3) = iProver_top
% 11.56/1.99      | v2_pre_topc(sK0) != iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_1084,c_1062]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_2642,plain,
% 11.56/1.99      ( m1_pre_topc(X0_51,sK2) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,sK3) = iProver_top ),
% 11.56/1.99      inference(global_propositional_subsumption,
% 11.56/1.99                [status(thm)],
% 11.56/1.99                [c_2085,c_38,c_39,c_46,c_49,c_1675,c_2010,c_2076]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_2648,plain,
% 11.56/1.99      ( m1_pre_topc(sK4,sK3) = iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_1080,c_2642]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_16,negated_conjecture,
% 11.56/1.99      ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 11.56/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_480,negated_conjecture,
% 11.56/1.99      ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_16]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1073,plain,
% 11.56/1.99      ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_5,plain,
% 11.56/1.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.56/1.99      | ~ m1_pre_topc(X3,X4)
% 11.56/1.99      | ~ m1_pre_topc(X3,X1)
% 11.56/1.99      | ~ m1_pre_topc(X1,X4)
% 11.56/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.56/1.99      | v2_struct_0(X4)
% 11.56/1.99      | v2_struct_0(X2)
% 11.56/1.99      | ~ l1_pre_topc(X4)
% 11.56/1.99      | ~ l1_pre_topc(X2)
% 11.56/1.99      | ~ v2_pre_topc(X4)
% 11.56/1.99      | ~ v2_pre_topc(X2)
% 11.56/1.99      | ~ v1_funct_1(X0)
% 11.56/1.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 11.56/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_488,plain,
% 11.56/1.99      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 11.56/1.99      | ~ m1_pre_topc(X2_51,X3_51)
% 11.56/1.99      | ~ m1_pre_topc(X0_51,X3_51)
% 11.56/1.99      | ~ m1_pre_topc(X2_51,X0_51)
% 11.56/1.99      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 11.56/1.99      | v2_struct_0(X1_51)
% 11.56/1.99      | v2_struct_0(X3_51)
% 11.56/1.99      | ~ l1_pre_topc(X1_51)
% 11.56/1.99      | ~ l1_pre_topc(X3_51)
% 11.56/1.99      | ~ v2_pre_topc(X1_51)
% 11.56/1.99      | ~ v2_pre_topc(X3_51)
% 11.56/1.99      | ~ v1_funct_1(X0_49)
% 11.56/1.99      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_49,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_49) ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_5]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1065,plain,
% 11.56/1.99      ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_49,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_49)
% 11.56/1.99      | v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 11.56/1.99      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,X3_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(X2_51,X3_51) != iProver_top
% 11.56/1.99      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 11.56/1.99      | v2_struct_0(X3_51) = iProver_top
% 11.56/1.99      | v2_struct_0(X1_51) = iProver_top
% 11.56/1.99      | l1_pre_topc(X3_51) != iProver_top
% 11.56/1.99      | l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X3_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v1_funct_1(X0_49) != iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_488]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_2413,plain,
% 11.56/1.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
% 11.56/1.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,sK2) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK2,X1_51) != iProver_top
% 11.56/1.99      | v2_struct_0(X1_51) = iProver_top
% 11.56/1.99      | v2_struct_0(sK1) = iProver_top
% 11.56/1.99      | l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) != iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_1073,c_1065]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_33,negated_conjecture,
% 11.56/1.99      ( ~ v2_struct_0(sK1) ),
% 11.56/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_40,plain,
% 11.56/1.99      ( v2_struct_0(sK1) != iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_32,negated_conjecture,
% 11.56/1.99      ( v2_pre_topc(sK1) ),
% 11.56/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_41,plain,
% 11.56/1.99      ( v2_pre_topc(sK1) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_31,negated_conjecture,
% 11.56/1.99      ( l1_pre_topc(sK1) ),
% 11.56/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_42,plain,
% 11.56/1.99      ( l1_pre_topc(sK1) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_19,negated_conjecture,
% 11.56/1.99      ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
% 11.56/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_54,plain,
% 11.56/1.99      ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_18,negated_conjecture,
% 11.56/1.99      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 11.56/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_55,plain,
% 11.56/1.99      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3857,plain,
% 11.56/1.99      ( l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
% 11.56/1.99      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,sK2) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK2,X1_51) != iProver_top
% 11.56/1.99      | v2_struct_0(X1_51) = iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top ),
% 11.56/1.99      inference(global_propositional_subsumption,
% 11.56/1.99                [status(thm)],
% 11.56/1.99                [c_2413,c_40,c_41,c_42,c_54,c_55]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3858,plain,
% 11.56/1.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
% 11.56/1.99      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,sK2) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK2,X1_51) != iProver_top
% 11.56/1.99      | v2_struct_0(X1_51) = iProver_top
% 11.56/1.99      | l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top ),
% 11.56/1.99      inference(renaming,[status(thm)],[c_3857]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3868,plain,
% 11.56/1.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)) = k3_tmap_1(sK3,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
% 11.56/1.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 11.56/1.99      | v2_struct_0(sK3) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK3) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK3) != iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_2648,c_3858]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_4,plain,
% 11.56/1.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.56/1.99      | ~ m1_pre_topc(X3,X1)
% 11.56/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.56/1.99      | v2_struct_0(X1)
% 11.56/1.99      | v2_struct_0(X2)
% 11.56/1.99      | ~ l1_pre_topc(X1)
% 11.56/1.99      | ~ l1_pre_topc(X2)
% 11.56/1.99      | ~ v2_pre_topc(X1)
% 11.56/1.99      | ~ v2_pre_topc(X2)
% 11.56/1.99      | ~ v1_funct_1(X0)
% 11.56/1.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 11.56/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_489,plain,
% 11.56/1.99      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 11.56/1.99      | ~ m1_pre_topc(X2_51,X0_51)
% 11.56/1.99      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 11.56/1.99      | v2_struct_0(X1_51)
% 11.56/1.99      | v2_struct_0(X0_51)
% 11.56/1.99      | ~ l1_pre_topc(X1_51)
% 11.56/1.99      | ~ l1_pre_topc(X0_51)
% 11.56/1.99      | ~ v2_pre_topc(X1_51)
% 11.56/1.99      | ~ v2_pre_topc(X0_51)
% 11.56/1.99      | ~ v1_funct_1(X0_49)
% 11.56/1.99      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_49,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_49,X2_51) ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_4]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1064,plain,
% 11.56/1.99      ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_49,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_49,X2_51)
% 11.56/1.99      | v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 11.56/1.99      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 11.56/1.99      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 11.56/1.99      | v2_struct_0(X1_51) = iProver_top
% 11.56/1.99      | v2_struct_0(X0_51) = iProver_top
% 11.56/1.99      | l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | l1_pre_topc(X0_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X0_51) != iProver_top
% 11.56/1.99      | v1_funct_1(X0_49) != iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_489]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_2193,plain,
% 11.56/1.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0_51)
% 11.56/1.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,sK2) != iProver_top
% 11.56/1.99      | v2_struct_0(sK2) = iProver_top
% 11.56/1.99      | v2_struct_0(sK1) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK2) != iProver_top
% 11.56/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK2) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) != iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_1073,c_1064]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_30,negated_conjecture,
% 11.56/1.99      ( ~ v2_struct_0(sK2) ),
% 11.56/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_43,plain,
% 11.56/1.99      ( v2_struct_0(sK2) != iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_29,negated_conjecture,
% 11.56/1.99      ( m1_pre_topc(sK2,sK0) ),
% 11.56/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_44,plain,
% 11.56/1.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1453,plain,
% 11.56/1.99      ( ~ m1_pre_topc(sK2,X0_51)
% 11.56/1.99      | ~ l1_pre_topc(X0_51)
% 11.56/1.99      | l1_pre_topc(sK2) ),
% 11.56/1.99      inference(instantiation,[status(thm)],[c_490]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_2006,plain,
% 11.56/1.99      ( ~ m1_pre_topc(sK2,sK0) | l1_pre_topc(sK2) | ~ l1_pre_topc(sK0) ),
% 11.56/1.99      inference(instantiation,[status(thm)],[c_1453]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_2007,plain,
% 11.56/1.99      ( m1_pre_topc(sK2,sK0) != iProver_top
% 11.56/1.99      | l1_pre_topc(sK2) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_2006]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_2074,plain,
% 11.56/1.99      ( l1_pre_topc(sK3) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK2) = iProver_top
% 11.56/1.99      | v2_pre_topc(sK3) != iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_1081,c_1062]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3703,plain,
% 11.56/1.99      ( m1_pre_topc(X0_51,sK2) != iProver_top
% 11.56/1.99      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0_51) ),
% 11.56/1.99      inference(global_propositional_subsumption,
% 11.56/1.99                [status(thm)],
% 11.56/1.99                [c_2193,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_46,c_54,
% 11.56/1.99                 c_55,c_2007,c_2010,c_2074,c_2076]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3704,plain,
% 11.56/1.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0_51)
% 11.56/1.99      | m1_pre_topc(X0_51,sK2) != iProver_top ),
% 11.56/1.99      inference(renaming,[status(thm)],[c_3703]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3709,plain,
% 11.56/1.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)) = k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4) ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_1080,c_3704]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3869,plain,
% 11.56/1.99      ( k3_tmap_1(sK3,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) = k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4)
% 11.56/1.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 11.56/1.99      | v2_struct_0(sK3) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK3) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK3) != iProver_top ),
% 11.56/1.99      inference(light_normalisation,[status(thm)],[c_3868,c_3709]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_28,negated_conjecture,
% 11.56/1.99      ( ~ v2_struct_0(sK3) ),
% 11.56/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_45,plain,
% 11.56/1.99      ( v2_struct_0(sK3) != iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_50,plain,
% 11.56/1.99      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_5025,plain,
% 11.56/1.99      ( k3_tmap_1(sK3,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) = k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4) ),
% 11.56/1.99      inference(global_propositional_subsumption,
% 11.56/1.99                [status(thm)],
% 11.56/1.99                [c_3869,c_38,c_39,c_45,c_46,c_49,c_50,c_2010,c_2076]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_467,negated_conjecture,
% 11.56/1.99      ( m1_pre_topc(sK2,sK0) ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_29]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1086,plain,
% 11.56/1.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_20,negated_conjecture,
% 11.56/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 11.56/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_476,negated_conjecture,
% 11.56/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_20]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1077,plain,
% 11.56/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_2414,plain,
% 11.56/1.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK3,X0_51,sK5)
% 11.56/1.99      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,sK3) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK3,X1_51) != iProver_top
% 11.56/1.99      | v2_struct_0(X1_51) = iProver_top
% 11.56/1.99      | v2_struct_0(sK1) = iProver_top
% 11.56/1.99      | l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v1_funct_1(sK5) != iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_1077,c_1065]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_22,negated_conjecture,
% 11.56/1.99      ( v1_funct_1(sK5) ),
% 11.56/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_51,plain,
% 11.56/1.99      ( v1_funct_1(sK5) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_21,negated_conjecture,
% 11.56/1.99      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 11.56/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_52,plain,
% 11.56/1.99      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3405,plain,
% 11.56/1.99      ( l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK3,X0_51,sK5)
% 11.56/1.99      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,sK3) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK3,X1_51) != iProver_top
% 11.56/1.99      | v2_struct_0(X1_51) = iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top ),
% 11.56/1.99      inference(global_propositional_subsumption,
% 11.56/1.99                [status(thm)],
% 11.56/1.99                [c_2414,c_40,c_41,c_42,c_51,c_52]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3406,plain,
% 11.56/1.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK3,X0_51,sK5)
% 11.56/1.99      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,sK3) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK3,X1_51) != iProver_top
% 11.56/1.99      | v2_struct_0(X1_51) = iProver_top
% 11.56/1.99      | l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top ),
% 11.56/1.99      inference(renaming,[status(thm)],[c_3405]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3415,plain,
% 11.56/1.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,sK5)
% 11.56/1.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 11.56/1.99      | v2_struct_0(sK0) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK0) != iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_1086,c_3406]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_2194,plain,
% 11.56/1.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0_51)) = k2_tmap_1(sK3,sK1,sK5,X0_51)
% 11.56/1.99      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,sK3) != iProver_top
% 11.56/1.99      | v2_struct_0(sK3) = iProver_top
% 11.56/1.99      | v2_struct_0(sK1) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK3) != iProver_top
% 11.56/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK3) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v1_funct_1(sK5) != iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_1077,c_1064]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3169,plain,
% 11.56/1.99      ( m1_pre_topc(X0_51,sK3) != iProver_top
% 11.56/1.99      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0_51)) = k2_tmap_1(sK3,sK1,sK5,X0_51) ),
% 11.56/1.99      inference(global_propositional_subsumption,
% 11.56/1.99                [status(thm)],
% 11.56/1.99                [c_2194,c_38,c_39,c_40,c_41,c_42,c_45,c_46,c_51,c_52,
% 11.56/1.99                 c_2010,c_2076]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3170,plain,
% 11.56/1.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0_51)) = k2_tmap_1(sK3,sK1,sK5,X0_51)
% 11.56/1.99      | m1_pre_topc(X0_51,sK3) != iProver_top ),
% 11.56/1.99      inference(renaming,[status(thm)],[c_3169]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3175,plain,
% 11.56/1.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK5,sK2) ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_1081,c_3170]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3418,plain,
% 11.56/1.99      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k2_tmap_1(sK3,sK1,sK5,sK2)
% 11.56/1.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 11.56/1.99      | v2_struct_0(sK0) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK0) != iProver_top ),
% 11.56/1.99      inference(light_normalisation,[status(thm)],[c_3415,c_3175]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_36,negated_conjecture,
% 11.56/1.99      ( ~ v2_struct_0(sK0) ),
% 11.56/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_37,plain,
% 11.56/1.99      ( v2_struct_0(sK0) != iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_4118,plain,
% 11.56/1.99      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k2_tmap_1(sK3,sK1,sK5,sK2) ),
% 11.56/1.99      inference(global_propositional_subsumption,
% 11.56/1.99                [status(thm)],
% 11.56/1.99                [c_3418,c_37,c_38,c_39,c_46,c_49]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_5027,plain,
% 11.56/1.99      ( k3_tmap_1(sK3,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) ),
% 11.56/1.99      inference(light_normalisation,[status(thm)],[c_5025,c_4118]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_9,plain,
% 11.56/1.99      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k2_tmap_1(X2,X1,X4,X3)),k2_tmap_1(X2,X1,X4,X0))
% 11.56/1.99      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
% 11.56/1.99      | ~ m1_pre_topc(X3,X2)
% 11.56/1.99      | ~ m1_pre_topc(X0,X2)
% 11.56/1.99      | ~ m1_pre_topc(X0,X3)
% 11.56/1.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 11.56/1.99      | v2_struct_0(X2)
% 11.56/1.99      | v2_struct_0(X1)
% 11.56/1.99      | v2_struct_0(X3)
% 11.56/1.99      | v2_struct_0(X0)
% 11.56/1.99      | ~ l1_pre_topc(X2)
% 11.56/1.99      | ~ l1_pre_topc(X1)
% 11.56/1.99      | ~ v2_pre_topc(X2)
% 11.56/1.99      | ~ v2_pre_topc(X1)
% 11.56/1.99      | ~ v1_funct_1(X4) ),
% 11.56/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_484,plain,
% 11.56/1.99      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k3_tmap_1(X2_51,X1_51,X3_51,X0_51,k2_tmap_1(X2_51,X1_51,X0_49,X3_51)),k2_tmap_1(X2_51,X1_51,X0_49,X0_51))
% 11.56/1.99      | ~ v1_funct_2(X0_49,u1_struct_0(X2_51),u1_struct_0(X1_51))
% 11.56/1.99      | ~ m1_pre_topc(X0_51,X3_51)
% 11.56/1.99      | ~ m1_pre_topc(X3_51,X2_51)
% 11.56/1.99      | ~ m1_pre_topc(X0_51,X2_51)
% 11.56/1.99      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
% 11.56/1.99      | v2_struct_0(X2_51)
% 11.56/1.99      | v2_struct_0(X1_51)
% 11.56/1.99      | v2_struct_0(X3_51)
% 11.56/1.99      | v2_struct_0(X0_51)
% 11.56/1.99      | ~ l1_pre_topc(X2_51)
% 11.56/1.99      | ~ l1_pre_topc(X1_51)
% 11.56/1.99      | ~ v2_pre_topc(X2_51)
% 11.56/1.99      | ~ v2_pre_topc(X1_51)
% 11.56/1.99      | ~ v1_funct_1(X0_49) ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_9]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1069,plain,
% 11.56/1.99      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k3_tmap_1(X2_51,X1_51,X3_51,X0_51,k2_tmap_1(X2_51,X1_51,X0_49,X3_51)),k2_tmap_1(X2_51,X1_51,X0_49,X0_51)) = iProver_top
% 11.56/1.99      | v1_funct_2(X0_49,u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top
% 11.56/1.99      | m1_pre_topc(X3_51,X2_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,X3_51) != iProver_top
% 11.56/1.99      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) != iProver_top
% 11.56/1.99      | v2_struct_0(X2_51) = iProver_top
% 11.56/1.99      | v2_struct_0(X3_51) = iProver_top
% 11.56/1.99      | v2_struct_0(X1_51) = iProver_top
% 11.56/1.99      | v2_struct_0(X0_51) = iProver_top
% 11.56/1.99      | l1_pre_topc(X2_51) != iProver_top
% 11.56/1.99      | l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X2_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v1_funct_1(X0_49) != iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_484]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_5031,plain,
% 11.56/1.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4)) = iProver_top
% 11.56/1.99      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 11.56/1.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 11.56/1.99      | v2_struct_0(sK2) = iProver_top
% 11.56/1.99      | v2_struct_0(sK4) = iProver_top
% 11.56/1.99      | v2_struct_0(sK3) = iProver_top
% 11.56/1.99      | v2_struct_0(sK1) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK3) != iProver_top
% 11.56/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK3) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v1_funct_1(sK5) != iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_5027,c_1069]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_26,negated_conjecture,
% 11.56/1.99      ( ~ v2_struct_0(sK4) ),
% 11.56/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_47,plain,
% 11.56/1.99      ( v2_struct_0(sK4) != iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_53,plain,
% 11.56/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_7744,plain,
% 11.56/1.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k2_tmap_1(sK3,sK1,sK5,sK4)) = iProver_top ),
% 11.56/1.99      inference(global_propositional_subsumption,
% 11.56/1.99                [status(thm)],
% 11.56/1.99                [c_5031,c_38,c_39,c_40,c_41,c_42,c_43,c_45,c_46,c_47,
% 11.56/1.99                 c_49,c_50,c_51,c_52,c_53,c_2010,c_2076,c_2648]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_6,plain,
% 11.56/1.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.56/1.99      | ~ m1_pre_topc(X3,X4)
% 11.56/1.99      | ~ m1_pre_topc(X1,X4)
% 11.56/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.56/1.99      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 11.56/1.99      | v2_struct_0(X4)
% 11.56/1.99      | v2_struct_0(X2)
% 11.56/1.99      | ~ l1_pre_topc(X4)
% 11.56/1.99      | ~ l1_pre_topc(X2)
% 11.56/1.99      | ~ v2_pre_topc(X4)
% 11.56/1.99      | ~ v2_pre_topc(X2)
% 11.56/1.99      | ~ v1_funct_1(X0) ),
% 11.56/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_487,plain,
% 11.56/1.99      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 11.56/1.99      | ~ m1_pre_topc(X2_51,X3_51)
% 11.56/1.99      | ~ m1_pre_topc(X0_51,X3_51)
% 11.56/1.99      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 11.56/1.99      | m1_subset_1(k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
% 11.56/1.99      | v2_struct_0(X1_51)
% 11.56/1.99      | v2_struct_0(X3_51)
% 11.56/1.99      | ~ l1_pre_topc(X1_51)
% 11.56/1.99      | ~ l1_pre_topc(X3_51)
% 11.56/1.99      | ~ v2_pre_topc(X1_51)
% 11.56/1.99      | ~ v2_pre_topc(X3_51)
% 11.56/1.99      | ~ v1_funct_1(X0_49) ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_6]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1066,plain,
% 11.56/1.99      ( v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(X3_51,X2_51) != iProver_top
% 11.56/1.99      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 11.56/1.99      | m1_subset_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51)))) = iProver_top
% 11.56/1.99      | v2_struct_0(X2_51) = iProver_top
% 11.56/1.99      | v2_struct_0(X1_51) = iProver_top
% 11.56/1.99      | l1_pre_topc(X2_51) != iProver_top
% 11.56/1.99      | l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X2_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v1_funct_1(X0_49) != iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_487]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_5029,plain,
% 11.56/1.99      ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 11.56/1.99      | m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top
% 11.56/1.99      | m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.56/1.99      | v2_struct_0(sK3) = iProver_top
% 11.56/1.99      | v2_struct_0(sK1) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK3) != iProver_top
% 11.56/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK3) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) != iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_5027,c_1066]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_4129,plain,
% 11.56/1.99      ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 11.56/1.99      inference(demodulation,[status(thm)],[c_4118,c_1073]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_478,negated_conjecture,
% 11.56/1.99      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_18]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1075,plain,
% 11.56/1.99      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_4130,plain,
% 11.56/1.99      ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 11.56/1.99      inference(demodulation,[status(thm)],[c_4118,c_1075]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_477,negated_conjecture,
% 11.56/1.99      ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_19]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1076,plain,
% 11.56/1.99      ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_477]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_4132,plain,
% 11.56/1.99      ( v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) = iProver_top ),
% 11.56/1.99      inference(demodulation,[status(thm)],[c_4118,c_1076]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_7385,plain,
% 11.56/1.99      ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
% 11.56/1.99      inference(global_propositional_subsumption,
% 11.56/1.99                [status(thm)],
% 11.56/1.99                [c_5029,c_38,c_39,c_40,c_41,c_42,c_45,c_46,c_49,c_2010,
% 11.56/1.99                 c_2076,c_2648,c_4129,c_4130,c_4132]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1,plain,
% 11.56/1.99      ( ~ r2_funct_2(X0,X1,X2,X3)
% 11.56/1.99      | ~ v1_funct_2(X3,X0,X1)
% 11.56/1.99      | ~ v1_funct_2(X2,X0,X1)
% 11.56/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.56/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.56/1.99      | ~ v1_funct_1(X3)
% 11.56/1.99      | ~ v1_funct_1(X2)
% 11.56/1.99      | X2 = X3 ),
% 11.56/1.99      inference(cnf_transformation,[],[f39]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_492,plain,
% 11.56/1.99      ( ~ r2_funct_2(X0_50,X1_50,X0_49,X1_49)
% 11.56/1.99      | ~ v1_funct_2(X1_49,X0_50,X1_50)
% 11.56/1.99      | ~ v1_funct_2(X0_49,X0_50,X1_50)
% 11.56/1.99      | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 11.56/1.99      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 11.56/1.99      | ~ v1_funct_1(X0_49)
% 11.56/1.99      | ~ v1_funct_1(X1_49)
% 11.56/1.99      | X0_49 = X1_49 ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_1]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1061,plain,
% 11.56/1.99      ( X0_49 = X1_49
% 11.56/1.99      | r2_funct_2(X0_50,X1_50,X0_49,X1_49) != iProver_top
% 11.56/1.99      | v1_funct_2(X0_49,X0_50,X1_50) != iProver_top
% 11.56/1.99      | v1_funct_2(X1_49,X0_50,X1_50) != iProver_top
% 11.56/1.99      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 11.56/1.99      | m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 11.56/1.99      | v1_funct_1(X0_49) != iProver_top
% 11.56/1.99      | v1_funct_1(X1_49) != iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_492]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_7392,plain,
% 11.56/1.99      ( k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = X0_49
% 11.56/1.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),X0_49) != iProver_top
% 11.56/1.99      | v1_funct_2(X0_49,u1_struct_0(sK4),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 11.56/1.99      | v1_funct_1(X0_49) != iProver_top
% 11.56/1.99      | v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) != iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_7385,c_1061]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_7,plain,
% 11.56/1.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.56/1.99      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 11.56/1.99      | ~ m1_pre_topc(X4,X3)
% 11.56/1.99      | ~ m1_pre_topc(X1,X3)
% 11.56/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.56/1.99      | v2_struct_0(X3)
% 11.56/1.99      | v2_struct_0(X2)
% 11.56/1.99      | ~ l1_pre_topc(X3)
% 11.56/1.99      | ~ l1_pre_topc(X2)
% 11.56/1.99      | ~ v2_pre_topc(X3)
% 11.56/1.99      | ~ v2_pre_topc(X2)
% 11.56/1.99      | ~ v1_funct_1(X0) ),
% 11.56/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_486,plain,
% 11.56/1.99      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 11.56/1.99      | v1_funct_2(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_49),u1_struct_0(X3_51),u1_struct_0(X1_51))
% 11.56/1.99      | ~ m1_pre_topc(X3_51,X2_51)
% 11.56/1.99      | ~ m1_pre_topc(X0_51,X2_51)
% 11.56/1.99      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 11.56/1.99      | v2_struct_0(X2_51)
% 11.56/1.99      | v2_struct_0(X1_51)
% 11.56/1.99      | ~ l1_pre_topc(X2_51)
% 11.56/1.99      | ~ l1_pre_topc(X1_51)
% 11.56/1.99      | ~ v2_pre_topc(X2_51)
% 11.56/1.99      | ~ v2_pre_topc(X1_51)
% 11.56/1.99      | ~ v1_funct_1(X0_49) ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_7]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1067,plain,
% 11.56/1.99      ( v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 11.56/1.99      | v1_funct_2(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_49),u1_struct_0(X3_51),u1_struct_0(X1_51)) = iProver_top
% 11.56/1.99      | m1_pre_topc(X3_51,X2_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 11.56/1.99      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 11.56/1.99      | v2_struct_0(X2_51) = iProver_top
% 11.56/1.99      | v2_struct_0(X1_51) = iProver_top
% 11.56/1.99      | l1_pre_topc(X2_51) != iProver_top
% 11.56/1.99      | l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X2_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v1_funct_1(X0_49) != iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_486]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_5030,plain,
% 11.56/1.99      ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) = iProver_top
% 11.56/1.99      | v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 11.56/1.99      | m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.56/1.99      | v2_struct_0(sK3) = iProver_top
% 11.56/1.99      | v2_struct_0(sK1) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK3) != iProver_top
% 11.56/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK3) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) != iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_5027,c_1067]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_8,plain,
% 11.56/1.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.56/1.99      | ~ m1_pre_topc(X3,X4)
% 11.56/1.99      | ~ m1_pre_topc(X1,X4)
% 11.56/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.56/1.99      | v2_struct_0(X4)
% 11.56/1.99      | v2_struct_0(X2)
% 11.56/1.99      | ~ l1_pre_topc(X4)
% 11.56/1.99      | ~ l1_pre_topc(X2)
% 11.56/1.99      | ~ v2_pre_topc(X4)
% 11.56/1.99      | ~ v2_pre_topc(X2)
% 11.56/1.99      | ~ v1_funct_1(X0)
% 11.56/1.99      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 11.56/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_485,plain,
% 11.56/1.99      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 11.56/1.99      | ~ m1_pre_topc(X2_51,X3_51)
% 11.56/1.99      | ~ m1_pre_topc(X0_51,X3_51)
% 11.56/1.99      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 11.56/1.99      | v2_struct_0(X1_51)
% 11.56/1.99      | v2_struct_0(X3_51)
% 11.56/1.99      | ~ l1_pre_topc(X1_51)
% 11.56/1.99      | ~ l1_pre_topc(X3_51)
% 11.56/1.99      | ~ v2_pre_topc(X1_51)
% 11.56/1.99      | ~ v2_pre_topc(X3_51)
% 11.56/1.99      | ~ v1_funct_1(X0_49)
% 11.56/1.99      | v1_funct_1(k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_49)) ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_8]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1068,plain,
% 11.56/1.99      ( v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(X3_51,X2_51) != iProver_top
% 11.56/1.99      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 11.56/1.99      | v2_struct_0(X2_51) = iProver_top
% 11.56/1.99      | v2_struct_0(X1_51) = iProver_top
% 11.56/1.99      | l1_pre_topc(X2_51) != iProver_top
% 11.56/1.99      | l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X2_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v1_funct_1(X0_49) != iProver_top
% 11.56/1.99      | v1_funct_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_49)) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_485]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_2202,plain,
% 11.56/1.99      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK2,X1_51) != iProver_top
% 11.56/1.99      | v2_struct_0(X1_51) = iProver_top
% 11.56/1.99      | v2_struct_0(sK1) = iProver_top
% 11.56/1.99      | l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))) = iProver_top
% 11.56/1.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) != iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_1073,c_1068]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3801,plain,
% 11.56/1.99      ( v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))) = iProver_top
% 11.56/1.99      | l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK2,X1_51) != iProver_top
% 11.56/1.99      | v2_struct_0(X1_51) = iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top ),
% 11.56/1.99      inference(global_propositional_subsumption,
% 11.56/1.99                [status(thm)],
% 11.56/1.99                [c_2202,c_40,c_41,c_42,c_54,c_55]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3802,plain,
% 11.56/1.99      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK2,X1_51) != iProver_top
% 11.56/1.99      | v2_struct_0(X1_51) = iProver_top
% 11.56/1.99      | l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))) = iProver_top ),
% 11.56/1.99      inference(renaming,[status(thm)],[c_3801]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_4124,plain,
% 11.56/1.99      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK2,X1_51) != iProver_top
% 11.56/1.99      | v2_struct_0(X1_51) = iProver_top
% 11.56/1.99      | l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,k2_tmap_1(sK3,sK1,sK5,sK2))) = iProver_top ),
% 11.56/1.99      inference(demodulation,[status(thm)],[c_4118,c_3802]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_5032,plain,
% 11.56/1.99      ( m1_pre_topc(sK2,sK3) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 11.56/1.99      | v2_struct_0(sK3) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK3) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK3) != iProver_top
% 11.56/1.99      | v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) = iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_5027,c_4124]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_7526,plain,
% 11.56/1.99      ( v1_funct_1(X0_49) != iProver_top
% 11.56/1.99      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 11.56/1.99      | k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = X0_49
% 11.56/1.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),X0_49) != iProver_top
% 11.56/1.99      | v1_funct_2(X0_49,u1_struct_0(sK4),u1_struct_0(sK1)) != iProver_top ),
% 11.56/1.99      inference(global_propositional_subsumption,
% 11.56/1.99                [status(thm)],
% 11.56/1.99                [c_7392,c_38,c_39,c_40,c_41,c_42,c_45,c_46,c_49,c_2010,
% 11.56/1.99                 c_2076,c_2648,c_4129,c_4130,c_4132,c_5030,c_5032]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_7527,plain,
% 11.56/1.99      ( k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = X0_49
% 11.56/1.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),X0_49) != iProver_top
% 11.56/1.99      | v1_funct_2(X0_49,u1_struct_0(sK4),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 11.56/1.99      | v1_funct_1(X0_49) != iProver_top ),
% 11.56/1.99      inference(renaming,[status(thm)],[c_7526]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_7748,plain,
% 11.56/1.99      ( k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k2_tmap_1(sK3,sK1,sK5,sK4)
% 11.56/1.99      | v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 11.56/1.99      | v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) != iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_7744,c_7527]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_25,negated_conjecture,
% 11.56/1.99      ( m1_pre_topc(sK4,sK0) ),
% 11.56/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_48,plain,
% 11.56/1.99      ( m1_pre_topc(sK4,sK0) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_471,negated_conjecture,
% 11.56/1.99      ( m1_pre_topc(sK4,sK0) ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_25]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1082,plain,
% 11.56/1.99      ( m1_pre_topc(sK4,sK0) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_471]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3413,plain,
% 11.56/1.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK3,sK4,sK5)
% 11.56/1.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 11.56/1.99      | v2_struct_0(sK0) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK0) != iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_1082,c_3406]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3176,plain,
% 11.56/1.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK3,sK1,sK5,sK4) ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_2648,c_3170]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3419,plain,
% 11.56/1.99      ( k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k2_tmap_1(sK3,sK1,sK5,sK4)
% 11.56/1.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 11.56/1.99      | v2_struct_0(sK0) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK0) != iProver_top ),
% 11.56/1.99      inference(light_normalisation,[status(thm)],[c_3413,c_3176]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_4744,plain,
% 11.56/1.99      ( k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k2_tmap_1(sK3,sK1,sK5,sK4) ),
% 11.56/1.99      inference(global_propositional_subsumption,
% 11.56/1.99                [status(thm)],
% 11.56/1.99                [c_3419,c_37,c_38,c_39,c_46,c_2648]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_4749,plain,
% 11.56/1.99      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 11.56/1.99      | m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top
% 11.56/1.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 11.56/1.99      | v2_struct_0(sK1) = iProver_top
% 11.56/1.99      | v2_struct_0(sK0) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.56/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v1_funct_1(sK5) != iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_4744,c_1066]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_4750,plain,
% 11.56/1.99      ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) = iProver_top
% 11.56/1.99      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 11.56/1.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 11.56/1.99      | v2_struct_0(sK1) = iProver_top
% 11.56/1.99      | v2_struct_0(sK0) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.56/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v1_funct_1(sK5) != iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_4744,c_1067]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_2203,plain,
% 11.56/1.99      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK3,X1_51) != iProver_top
% 11.56/1.99      | v2_struct_0(X1_51) = iProver_top
% 11.56/1.99      | v2_struct_0(sK1) = iProver_top
% 11.56/1.99      | l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v1_funct_1(k3_tmap_1(X1_51,sK1,sK3,X0_51,sK5)) = iProver_top
% 11.56/1.99      | v1_funct_1(sK5) != iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_1077,c_1068]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3194,plain,
% 11.56/1.99      ( v1_funct_1(k3_tmap_1(X1_51,sK1,sK3,X0_51,sK5)) = iProver_top
% 11.56/1.99      | l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK3,X1_51) != iProver_top
% 11.56/1.99      | v2_struct_0(X1_51) = iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top ),
% 11.56/1.99      inference(global_propositional_subsumption,
% 11.56/1.99                [status(thm)],
% 11.56/1.99                [c_2203,c_40,c_41,c_42,c_51,c_52]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_3195,plain,
% 11.56/1.99      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK3,X1_51) != iProver_top
% 11.56/1.99      | v2_struct_0(X1_51) = iProver_top
% 11.56/1.99      | l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v1_funct_1(k3_tmap_1(X1_51,sK1,sK3,X0_51,sK5)) = iProver_top ),
% 11.56/1.99      inference(renaming,[status(thm)],[c_3194]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_4751,plain,
% 11.56/1.99      ( m1_pre_topc(sK4,sK0) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 11.56/1.99      | v2_struct_0(sK0) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) = iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_4744,c_3195]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_18264,plain,
% 11.56/1.99      ( k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k2_tmap_1(sK3,sK1,sK5,sK4) ),
% 11.56/1.99      inference(global_propositional_subsumption,
% 11.56/1.99                [status(thm)],
% 11.56/1.99                [c_7748,c_37,c_38,c_39,c_40,c_41,c_42,c_46,c_48,c_51,
% 11.56/1.99                 c_52,c_53,c_4749,c_4750,c_4751]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_12,plain,
% 11.56/1.99      ( ~ v5_pre_topc(X0,X1,X2)
% 11.56/1.99      | v5_pre_topc(k3_tmap_1(X3,X2,X1,X4,X0),X4,X2)
% 11.56/1.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.56/1.99      | ~ m1_pre_topc(X4,X3)
% 11.56/1.99      | ~ m1_pre_topc(X4,X1)
% 11.56/1.99      | ~ m1_pre_topc(X1,X3)
% 11.56/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.56/1.99      | v2_struct_0(X3)
% 11.56/1.99      | v2_struct_0(X2)
% 11.56/1.99      | v2_struct_0(X4)
% 11.56/1.99      | v2_struct_0(X1)
% 11.56/1.99      | ~ l1_pre_topc(X3)
% 11.56/1.99      | ~ l1_pre_topc(X2)
% 11.56/1.99      | ~ v2_pre_topc(X3)
% 11.56/1.99      | ~ v2_pre_topc(X2)
% 11.56/1.99      | ~ v1_funct_1(X0) ),
% 11.56/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_482,plain,
% 11.56/1.99      ( ~ v5_pre_topc(X0_49,X0_51,X1_51)
% 11.56/1.99      | v5_pre_topc(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_49),X3_51,X1_51)
% 11.56/1.99      | ~ v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 11.56/1.99      | ~ m1_pre_topc(X3_51,X2_51)
% 11.56/1.99      | ~ m1_pre_topc(X0_51,X2_51)
% 11.56/1.99      | ~ m1_pre_topc(X3_51,X0_51)
% 11.56/1.99      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 11.56/1.99      | v2_struct_0(X2_51)
% 11.56/1.99      | v2_struct_0(X1_51)
% 11.56/1.99      | v2_struct_0(X3_51)
% 11.56/1.99      | v2_struct_0(X0_51)
% 11.56/1.99      | ~ l1_pre_topc(X2_51)
% 11.56/1.99      | ~ l1_pre_topc(X1_51)
% 11.56/1.99      | ~ v2_pre_topc(X2_51)
% 11.56/1.99      | ~ v2_pre_topc(X1_51)
% 11.56/1.99      | ~ v1_funct_1(X0_49) ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_12]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1071,plain,
% 11.56/1.99      ( v5_pre_topc(X0_49,X0_51,X1_51) != iProver_top
% 11.56/1.99      | v5_pre_topc(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_49),X3_51,X1_51) = iProver_top
% 11.56/1.99      | v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 11.56/1.99      | m1_pre_topc(X3_51,X2_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 11.56/1.99      | m1_pre_topc(X3_51,X0_51) != iProver_top
% 11.56/1.99      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 11.56/1.99      | v2_struct_0(X2_51) = iProver_top
% 11.56/1.99      | v2_struct_0(X3_51) = iProver_top
% 11.56/1.99      | v2_struct_0(X1_51) = iProver_top
% 11.56/1.99      | v2_struct_0(X0_51) = iProver_top
% 11.56/1.99      | l1_pre_topc(X2_51) != iProver_top
% 11.56/1.99      | l1_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X2_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(X1_51) != iProver_top
% 11.56/1.99      | v1_funct_1(X0_49) != iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_482]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_5028,plain,
% 11.56/1.99      ( v5_pre_topc(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),sK4,sK1) = iProver_top
% 11.56/1.99      | v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK2),sK2,sK1) != iProver_top
% 11.56/1.99      | v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 11.56/1.99      | m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.56/1.99      | v2_struct_0(sK2) = iProver_top
% 11.56/1.99      | v2_struct_0(sK4) = iProver_top
% 11.56/1.99      | v2_struct_0(sK3) = iProver_top
% 11.56/1.99      | v2_struct_0(sK1) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK3) != iProver_top
% 11.56/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK3) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) != iProver_top ),
% 11.56/1.99      inference(superposition,[status(thm)],[c_5027,c_1071]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_17,negated_conjecture,
% 11.56/1.99      ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) ),
% 11.56/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_479,negated_conjecture,
% 11.56/1.99      ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_17]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1074,plain,
% 11.56/1.99      ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_4131,plain,
% 11.56/1.99      ( v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK2),sK2,sK1) = iProver_top ),
% 11.56/1.99      inference(demodulation,[status(thm)],[c_4118,c_1074]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_7751,plain,
% 11.56/1.99      ( v5_pre_topc(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),sK4,sK1) = iProver_top ),
% 11.56/1.99      inference(global_propositional_subsumption,
% 11.56/1.99                [status(thm)],
% 11.56/1.99                [c_5028,c_38,c_39,c_40,c_41,c_42,c_43,c_45,c_46,c_47,
% 11.56/1.99                 c_49,c_50,c_2010,c_2076,c_2648,c_4129,c_4130,c_4131,
% 11.56/1.99                 c_4132]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_18273,plain,
% 11.56/1.99      ( v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1) = iProver_top ),
% 11.56/1.99      inference(demodulation,[status(thm)],[c_18264,c_7751]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_15,negated_conjecture,
% 11.56/1.99      ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
% 11.56/1.99      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
% 11.56/1.99      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
% 11.56/1.99      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) ),
% 11.56/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_481,negated_conjecture,
% 11.56/1.99      ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
% 11.56/1.99      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
% 11.56/1.99      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
% 11.56/1.99      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) ),
% 11.56/1.99      inference(subtyping,[status(esa)],[c_15]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1072,plain,
% 11.56/1.99      ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) != iProver_top
% 11.56/1.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 11.56/1.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) != iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_58,plain,
% 11.56/1.99      ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) != iProver_top
% 11.56/1.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 11.56/1.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) != iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1200,plain,
% 11.56/1.99      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(sK1))
% 11.56/1.99      | ~ m1_pre_topc(X0_51,X1_51)
% 11.56/1.99      | ~ m1_pre_topc(X2_51,X1_51)
% 11.56/1.99      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
% 11.56/1.99      | v2_struct_0(X1_51)
% 11.56/1.99      | v2_struct_0(sK1)
% 11.56/1.99      | ~ l1_pre_topc(X1_51)
% 11.56/1.99      | ~ l1_pre_topc(sK1)
% 11.56/1.99      | ~ v2_pre_topc(X1_51)
% 11.56/1.99      | ~ v2_pre_topc(sK1)
% 11.56/1.99      | ~ v1_funct_1(X0_49)
% 11.56/1.99      | v1_funct_1(k3_tmap_1(X1_51,sK1,X0_51,X2_51,X0_49)) ),
% 11.56/1.99      inference(instantiation,[status(thm)],[c_485]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1443,plain,
% 11.56/1.99      ( ~ v1_funct_2(X0_49,u1_struct_0(sK3),u1_struct_0(sK1))
% 11.56/1.99      | ~ m1_pre_topc(X0_51,sK0)
% 11.56/1.99      | ~ m1_pre_topc(sK3,sK0)
% 11.56/1.99      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 11.56/1.99      | v2_struct_0(sK1)
% 11.56/1.99      | v2_struct_0(sK0)
% 11.56/1.99      | ~ l1_pre_topc(sK1)
% 11.56/1.99      | ~ l1_pre_topc(sK0)
% 11.56/1.99      | ~ v2_pre_topc(sK1)
% 11.56/1.99      | ~ v2_pre_topc(sK0)
% 11.56/1.99      | ~ v1_funct_1(X0_49)
% 11.56/1.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0_51,X0_49)) ),
% 11.56/1.99      inference(instantiation,[status(thm)],[c_1200]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1764,plain,
% 11.56/1.99      ( ~ v1_funct_2(X0_49,u1_struct_0(sK3),u1_struct_0(sK1))
% 11.56/1.99      | ~ m1_pre_topc(sK4,sK0)
% 11.56/1.99      | ~ m1_pre_topc(sK3,sK0)
% 11.56/1.99      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 11.56/1.99      | v2_struct_0(sK1)
% 11.56/1.99      | v2_struct_0(sK0)
% 11.56/1.99      | ~ l1_pre_topc(sK1)
% 11.56/1.99      | ~ l1_pre_topc(sK0)
% 11.56/1.99      | ~ v2_pre_topc(sK1)
% 11.56/1.99      | ~ v2_pre_topc(sK0)
% 11.56/1.99      | ~ v1_funct_1(X0_49)
% 11.56/1.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,X0_49)) ),
% 11.56/1.99      inference(instantiation,[status(thm)],[c_1443]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1765,plain,
% 11.56/1.99      ( v1_funct_2(X0_49,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 11.56/1.99      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 11.56/1.99      | v2_struct_0(sK1) = iProver_top
% 11.56/1.99      | v2_struct_0(sK0) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.56/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v1_funct_1(X0_49) != iProver_top
% 11.56/1.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,X0_49)) = iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_1764]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1767,plain,
% 11.56/1.99      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 11.56/1.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 11.56/1.99      | v2_struct_0(sK1) = iProver_top
% 11.56/1.99      | v2_struct_0(sK0) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.56/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) = iProver_top
% 11.56/1.99      | v1_funct_1(sK5) != iProver_top ),
% 11.56/1.99      inference(instantiation,[status(thm)],[c_1765]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1198,plain,
% 11.56/1.99      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(sK1))
% 11.56/1.99      | ~ m1_pre_topc(X0_51,X1_51)
% 11.56/1.99      | ~ m1_pre_topc(X2_51,X1_51)
% 11.56/1.99      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
% 11.56/1.99      | m1_subset_1(k3_tmap_1(X1_51,sK1,X0_51,X2_51,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(sK1))))
% 11.56/1.99      | v2_struct_0(X1_51)
% 11.56/1.99      | v2_struct_0(sK1)
% 11.56/1.99      | ~ l1_pre_topc(X1_51)
% 11.56/1.99      | ~ l1_pre_topc(sK1)
% 11.56/1.99      | ~ v2_pre_topc(X1_51)
% 11.56/1.99      | ~ v2_pre_topc(sK1)
% 11.56/1.99      | ~ v1_funct_1(X0_49) ),
% 11.56/1.99      inference(instantiation,[status(thm)],[c_487]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1507,plain,
% 11.56/1.99      ( ~ v1_funct_2(X0_49,u1_struct_0(sK3),u1_struct_0(sK1))
% 11.56/1.99      | ~ m1_pre_topc(X0_51,sK0)
% 11.56/1.99      | ~ m1_pre_topc(sK3,sK0)
% 11.56/1.99      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 11.56/1.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0_51,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
% 11.56/1.99      | v2_struct_0(sK1)
% 11.56/1.99      | v2_struct_0(sK0)
% 11.56/1.99      | ~ l1_pre_topc(sK1)
% 11.56/1.99      | ~ l1_pre_topc(sK0)
% 11.56/1.99      | ~ v2_pre_topc(sK1)
% 11.56/1.99      | ~ v2_pre_topc(sK0)
% 11.56/1.99      | ~ v1_funct_1(X0_49) ),
% 11.56/1.99      inference(instantiation,[status(thm)],[c_1198]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1858,plain,
% 11.56/1.99      ( ~ v1_funct_2(X0_49,u1_struct_0(sK3),u1_struct_0(sK1))
% 11.56/1.99      | ~ m1_pre_topc(sK4,sK0)
% 11.56/1.99      | ~ m1_pre_topc(sK3,sK0)
% 11.56/1.99      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 11.56/1.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
% 11.56/1.99      | v2_struct_0(sK1)
% 11.56/1.99      | v2_struct_0(sK0)
% 11.56/1.99      | ~ l1_pre_topc(sK1)
% 11.56/1.99      | ~ l1_pre_topc(sK0)
% 11.56/1.99      | ~ v2_pre_topc(sK1)
% 11.56/1.99      | ~ v2_pre_topc(sK0)
% 11.56/1.99      | ~ v1_funct_1(X0_49) ),
% 11.56/1.99      inference(instantiation,[status(thm)],[c_1507]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1859,plain,
% 11.56/1.99      ( v1_funct_2(X0_49,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 11.56/1.99      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 11.56/1.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top
% 11.56/1.99      | v2_struct_0(sK1) = iProver_top
% 11.56/1.99      | v2_struct_0(sK0) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.56/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v1_funct_1(X0_49) != iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_1858]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1861,plain,
% 11.56/1.99      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 11.56/1.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top
% 11.56/1.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 11.56/1.99      | v2_struct_0(sK1) = iProver_top
% 11.56/1.99      | v2_struct_0(sK0) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.56/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v1_funct_1(sK5) != iProver_top ),
% 11.56/1.99      inference(instantiation,[status(thm)],[c_1859]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1155,plain,
% 11.56/1.99      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 11.56/1.99      | v1_funct_2(k3_tmap_1(sK0,X1_51,X0_51,X2_51,X0_49),u1_struct_0(X2_51),u1_struct_0(X1_51))
% 11.56/1.99      | ~ m1_pre_topc(X2_51,sK0)
% 11.56/1.99      | ~ m1_pre_topc(X0_51,sK0)
% 11.56/1.99      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 11.56/1.99      | v2_struct_0(X1_51)
% 11.56/1.99      | v2_struct_0(sK0)
% 11.56/1.99      | ~ l1_pre_topc(X1_51)
% 11.56/1.99      | ~ l1_pre_topc(sK0)
% 11.56/1.99      | ~ v2_pre_topc(X1_51)
% 11.56/1.99      | ~ v2_pre_topc(sK0)
% 11.56/1.99      | ~ v1_funct_1(X0_49) ),
% 11.56/1.99      inference(instantiation,[status(thm)],[c_486]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1519,plain,
% 11.56/1.99      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 11.56/1.99      | v1_funct_2(k3_tmap_1(sK0,X1_51,X0_51,sK4,X0_49),u1_struct_0(sK4),u1_struct_0(X1_51))
% 11.56/1.99      | ~ m1_pre_topc(X0_51,sK0)
% 11.56/1.99      | ~ m1_pre_topc(sK4,sK0)
% 11.56/1.99      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 11.56/1.99      | v2_struct_0(X1_51)
% 11.56/1.99      | v2_struct_0(sK0)
% 11.56/1.99      | ~ l1_pre_topc(X1_51)
% 11.56/1.99      | ~ l1_pre_topc(sK0)
% 11.56/1.99      | ~ v2_pre_topc(X1_51)
% 11.56/1.99      | ~ v2_pre_topc(sK0)
% 11.56/1.99      | ~ v1_funct_1(X0_49) ),
% 11.56/1.99      inference(instantiation,[status(thm)],[c_1155]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1919,plain,
% 11.56/1.99      ( ~ v1_funct_2(X0_49,u1_struct_0(sK3),u1_struct_0(X0_51))
% 11.56/1.99      | v1_funct_2(k3_tmap_1(sK0,X0_51,sK3,sK4,X0_49),u1_struct_0(sK4),u1_struct_0(X0_51))
% 11.56/1.99      | ~ m1_pre_topc(sK4,sK0)
% 11.56/1.99      | ~ m1_pre_topc(sK3,sK0)
% 11.56/1.99      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
% 11.56/1.99      | v2_struct_0(X0_51)
% 11.56/1.99      | v2_struct_0(sK0)
% 11.56/1.99      | ~ l1_pre_topc(X0_51)
% 11.56/1.99      | ~ l1_pre_topc(sK0)
% 11.56/1.99      | ~ v2_pre_topc(X0_51)
% 11.56/1.99      | ~ v2_pre_topc(sK0)
% 11.56/1.99      | ~ v1_funct_1(X0_49) ),
% 11.56/1.99      inference(instantiation,[status(thm)],[c_1519]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1920,plain,
% 11.56/1.99      ( v1_funct_2(X0_49,u1_struct_0(sK3),u1_struct_0(X0_51)) != iProver_top
% 11.56/1.99      | v1_funct_2(k3_tmap_1(sK0,X0_51,sK3,sK4,X0_49),u1_struct_0(sK4),u1_struct_0(X0_51)) = iProver_top
% 11.56/1.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 11.56/1.99      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51)))) != iProver_top
% 11.56/1.99      | v2_struct_0(X0_51) = iProver_top
% 11.56/1.99      | v2_struct_0(sK0) = iProver_top
% 11.56/1.99      | l1_pre_topc(X0_51) != iProver_top
% 11.56/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v2_pre_topc(X0_51) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v1_funct_1(X0_49) != iProver_top ),
% 11.56/1.99      inference(predicate_to_equality,[status(thm)],[c_1919]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_1922,plain,
% 11.56/1.99      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) = iProver_top
% 11.56/1.99      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 11.56/1.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 11.56/1.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 11.56/1.99      | v2_struct_0(sK1) = iProver_top
% 11.56/1.99      | v2_struct_0(sK0) = iProver_top
% 11.56/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.56/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.56/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.56/1.99      | v1_funct_1(sK5) != iProver_top ),
% 11.56/1.99      inference(instantiation,[status(thm)],[c_1920]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_2125,plain,
% 11.56/1.99      ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) != iProver_top ),
% 11.56/1.99      inference(global_propositional_subsumption,
% 11.56/1.99                [status(thm)],
% 11.56/1.99                [c_1072,c_37,c_38,c_39,c_40,c_41,c_42,c_46,c_48,c_51,
% 11.56/1.99                 c_52,c_53,c_58,c_1767,c_1861,c_1922]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(c_4746,plain,
% 11.56/1.99      ( v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1) != iProver_top ),
% 11.56/1.99      inference(demodulation,[status(thm)],[c_4744,c_2125]) ).
% 11.56/1.99  
% 11.56/1.99  cnf(contradiction,plain,
% 11.56/1.99      ( $false ),
% 11.56/1.99      inference(minisat,[status(thm)],[c_18273,c_4746]) ).
% 11.56/1.99  
% 11.56/1.99  
% 11.56/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.56/1.99  
% 11.56/1.99  ------                               Statistics
% 11.56/1.99  
% 11.56/1.99  ------ General
% 11.56/1.99  
% 11.56/1.99  abstr_ref_over_cycles:                  0
% 11.56/1.99  abstr_ref_under_cycles:                 0
% 11.56/1.99  gc_basic_clause_elim:                   0
% 11.56/1.99  forced_gc_time:                         0
% 11.56/1.99  parsing_time:                           0.01
% 11.56/1.99  unif_index_cands_time:                  0.
% 11.56/1.99  unif_index_add_time:                    0.
% 11.56/1.99  orderings_time:                         0.
% 11.56/1.99  out_proof_time:                         0.037
% 11.56/1.99  total_time:                             1.485
% 11.56/1.99  num_of_symbols:                         54
% 11.56/1.99  num_of_terms:                           22804
% 11.56/1.99  
% 11.56/1.99  ------ Preprocessing
% 11.56/1.99  
% 11.56/1.99  num_of_splits:                          0
% 11.56/1.99  num_of_split_atoms:                     0
% 11.56/1.99  num_of_reused_defs:                     0
% 11.56/1.99  num_eq_ax_congr_red:                    33
% 11.56/1.99  num_of_sem_filtered_clauses:            1
% 11.56/1.99  num_of_subtypes:                        5
% 11.56/1.99  monotx_restored_types:                  0
% 11.56/1.99  sat_num_of_epr_types:                   0
% 11.56/1.99  sat_num_of_non_cyclic_types:            0
% 11.56/1.99  sat_guarded_non_collapsed_types:        1
% 11.56/1.99  num_pure_diseq_elim:                    0
% 11.56/1.99  simp_replaced_by:                       0
% 11.56/1.99  res_preprocessed:                       122
% 11.56/1.99  prep_upred:                             0
% 11.56/1.99  prep_unflattend:                        8
% 11.56/1.99  smt_new_axioms:                         0
% 11.56/1.99  pred_elim_cands:                        9
% 11.56/1.99  pred_elim:                              0
% 11.56/1.99  pred_elim_cl:                           0
% 11.56/1.99  pred_elim_cycles:                       1
% 11.56/1.99  merged_defs:                            0
% 11.56/1.99  merged_defs_ncl:                        0
% 11.56/1.99  bin_hyper_res:                          0
% 11.56/1.99  prep_cycles:                            3
% 11.56/1.99  pred_elim_time:                         0.003
% 11.56/1.99  splitting_time:                         0.
% 11.56/1.99  sem_filter_time:                        0.
% 11.56/1.99  monotx_time:                            0.
% 11.56/1.99  subtype_inf_time:                       0.001
% 11.56/1.99  
% 11.56/1.99  ------ Problem properties
% 11.56/1.99  
% 11.56/1.99  clauses:                                37
% 11.56/1.99  conjectures:                            22
% 11.56/1.99  epr:                                    18
% 11.56/1.99  horn:                                   27
% 11.56/1.99  ground:                                 22
% 11.56/1.99  unary:                                  21
% 11.56/1.99  binary:                                 0
% 11.56/1.99  lits:                                   176
% 11.56/1.99  lits_eq:                                3
% 11.56/1.99  fd_pure:                                0
% 11.56/1.99  fd_pseudo:                              0
% 11.56/1.99  fd_cond:                                0
% 11.56/1.99  fd_pseudo_cond:                         1
% 11.56/1.99  ac_symbols:                             0
% 11.56/1.99  
% 11.56/1.99  ------ Propositional Solver
% 11.56/1.99  
% 11.56/1.99  prop_solver_calls:                      28
% 11.56/1.99  prop_fast_solver_calls:                 3339
% 11.56/1.99  smt_solver_calls:                       0
% 11.56/1.99  smt_fast_solver_calls:                  0
% 11.56/1.99  prop_num_of_clauses:                    9686
% 11.56/1.99  prop_preprocess_simplified:             18740
% 11.56/1.99  prop_fo_subsumed:                       867
% 11.56/1.99  prop_solver_time:                       0.
% 11.56/1.99  smt_solver_time:                        0.
% 11.56/1.99  smt_fast_solver_time:                   0.
% 11.56/1.99  prop_fast_solver_time:                  0.
% 11.56/1.99  prop_unsat_core_time:                   0.004
% 11.56/1.99  
% 11.56/1.99  ------ QBF
% 11.56/1.99  
% 11.56/1.99  qbf_q_res:                              0
% 11.56/1.99  qbf_num_tautologies:                    0
% 11.56/1.99  qbf_prep_cycles:                        0
% 11.56/1.99  
% 11.56/1.99  ------ BMC1
% 11.56/1.99  
% 11.56/1.99  bmc1_current_bound:                     -1
% 11.56/1.99  bmc1_last_solved_bound:                 -1
% 11.56/1.99  bmc1_unsat_core_size:                   -1
% 11.56/1.99  bmc1_unsat_core_parents_size:           -1
% 11.56/1.99  bmc1_merge_next_fun:                    0
% 11.56/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.56/1.99  
% 11.56/1.99  ------ Instantiation
% 11.56/1.99  
% 11.56/1.99  inst_num_of_clauses:                    2868
% 11.56/1.99  inst_num_in_passive:                    815
% 11.56/1.99  inst_num_in_active:                     974
% 11.56/1.99  inst_num_in_unprocessed:                1079
% 11.56/1.99  inst_num_of_loops:                      1080
% 11.56/1.99  inst_num_of_learning_restarts:          0
% 11.56/1.99  inst_num_moves_active_passive:          104
% 11.56/1.99  inst_lit_activity:                      0
% 11.56/1.99  inst_lit_activity_moves:                2
% 11.56/1.99  inst_num_tautologies:                   0
% 11.56/1.99  inst_num_prop_implied:                  0
% 11.56/1.99  inst_num_existing_simplified:           0
% 11.56/1.99  inst_num_eq_res_simplified:             0
% 11.56/1.99  inst_num_child_elim:                    0
% 11.56/1.99  inst_num_of_dismatching_blockings:      202
% 11.56/1.99  inst_num_of_non_proper_insts:           1569
% 11.56/1.99  inst_num_of_duplicates:                 0
% 11.56/1.99  inst_inst_num_from_inst_to_res:         0
% 11.56/1.99  inst_dismatching_checking_time:         0.
% 11.56/1.99  
% 11.56/1.99  ------ Resolution
% 11.56/1.99  
% 11.56/1.99  res_num_of_clauses:                     0
% 11.56/1.99  res_num_in_passive:                     0
% 11.56/1.99  res_num_in_active:                      0
% 11.56/1.99  res_num_of_loops:                       125
% 11.56/1.99  res_forward_subset_subsumed:            21
% 11.56/1.99  res_backward_subset_subsumed:           0
% 11.56/1.99  res_forward_subsumed:                   0
% 11.56/1.99  res_backward_subsumed:                  0
% 11.56/1.99  res_forward_subsumption_resolution:     1
% 11.56/1.99  res_backward_subsumption_resolution:    0
% 11.56/1.99  res_clause_to_clause_subsumption:       583
% 11.56/1.99  res_orphan_elimination:                 0
% 11.56/1.99  res_tautology_del:                      26
% 11.56/1.99  res_num_eq_res_simplified:              0
% 11.56/1.99  res_num_sel_changes:                    0
% 11.56/1.99  res_moves_from_active_to_pass:          0
% 11.56/1.99  
% 11.56/1.99  ------ Superposition
% 11.56/1.99  
% 11.56/1.99  sup_time_total:                         0.
% 11.56/1.99  sup_time_generating:                    0.
% 11.56/1.99  sup_time_sim_full:                      0.
% 11.56/1.99  sup_time_sim_immed:                     0.
% 11.56/1.99  
% 11.56/1.99  sup_num_of_clauses:                     254
% 11.56/1.99  sup_num_in_active:                      177
% 11.56/1.99  sup_num_in_passive:                     77
% 11.56/1.99  sup_num_of_loops:                       214
% 11.56/1.99  sup_fw_superposition:                   189
% 11.56/1.99  sup_bw_superposition:                   126
% 11.56/1.99  sup_immediate_simplified:               80
% 11.56/1.99  sup_given_eliminated:                   3
% 11.56/1.99  comparisons_done:                       0
% 11.56/1.99  comparisons_avoided:                    0
% 11.56/1.99  
% 11.56/1.99  ------ Simplifications
% 11.56/1.99  
% 11.56/1.99  
% 11.56/1.99  sim_fw_subset_subsumed:                 12
% 11.56/1.99  sim_bw_subset_subsumed:                 9
% 11.56/1.99  sim_fw_subsumed:                        17
% 11.56/1.99  sim_bw_subsumed:                        3
% 11.56/1.99  sim_fw_subsumption_res:                 0
% 11.56/1.99  sim_bw_subsumption_res:                 0
% 11.56/1.99  sim_tautology_del:                      0
% 11.56/1.99  sim_eq_tautology_del:                   8
% 11.56/1.99  sim_eq_res_simp:                        0
% 11.56/1.99  sim_fw_demodulated:                     14
% 11.56/1.99  sim_bw_demodulated:                     34
% 11.56/1.99  sim_light_normalised:                   77
% 11.56/1.99  sim_joinable_taut:                      0
% 11.56/1.99  sim_joinable_simp:                      0
% 11.56/1.99  sim_ac_normalised:                      0
% 11.56/1.99  sim_smt_subsumption:                    0
% 11.56/1.99  
%------------------------------------------------------------------------------
