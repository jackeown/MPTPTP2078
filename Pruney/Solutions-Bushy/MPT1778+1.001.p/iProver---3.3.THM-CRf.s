%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1778+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:22 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :  192 (3940 expanded)
%              Number of clauses        :  131 ( 840 expanded)
%              Number of leaves         :   14 (1581 expanded)
%              Depth                    :   23
%              Number of atoms          : 1443 (65709 expanded)
%              Number of equality atoms :  302 (1250 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   38 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X3] :
                      ( r1_tmap_1(X1,X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ( ~ r1_tmap_1(X1,X0,X2,sK1(X0,X1,X2))
                    & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_tmap_1(X1,X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X3,X2)
                         => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                      & m1_pre_topc(X3,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                      & m1_pre_topc(X3,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
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
    inference(flattening,[],[f20])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
            | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
            | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
          & m1_pre_topc(X3,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(X4,X2,X1)
          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,sK6),X3,X1)
          | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,sK6),u1_struct_0(X3),u1_struct_0(X1))
          | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,sK6)) )
        & m1_pre_topc(X3,X2)
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(sK6,X2,X1)
        & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
              & m1_pre_topc(X3,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v5_pre_topc(X4,X2,X1)
              & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,sK5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
              | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,sK5,X4),sK5,X1)
              | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,sK5,X4),u1_struct_0(sK5),u1_struct_0(X1))
              | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,sK5,X4)) )
            & m1_pre_topc(sK5,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v5_pre_topc(X4,X2,X1)
            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                    | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                    | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                  & m1_pre_topc(X3,X2)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v5_pre_topc(X4,X2,X1)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,sK4,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k3_tmap_1(X0,X1,sK4,X3,X4),X3,X1)
                  | ~ v1_funct_2(k3_tmap_1(X0,X1,sK4,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                  | ~ v1_funct_1(k3_tmap_1(X0,X1,sK4,X3,X4)) )
                & m1_pre_topc(X3,sK4)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
                & v5_pre_topc(X4,sK4,X1)
                & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                      & m1_pre_topc(X3,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
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
                    ( ( ~ m1_subset_1(k3_tmap_1(X0,sK3,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                      | ~ v5_pre_topc(k3_tmap_1(X0,sK3,X2,X3,X4),X3,sK3)
                      | ~ v1_funct_2(k3_tmap_1(X0,sK3,X2,X3,X4),u1_struct_0(X3),u1_struct_0(sK3))
                      | ~ v1_funct_1(k3_tmap_1(X0,sK3,X2,X3,X4)) )
                    & m1_pre_topc(X3,X2)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                    & v5_pre_topc(X4,X2,sK3)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                          | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                        & m1_pre_topc(X3,X2)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
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
                      ( ( ~ m1_subset_1(k3_tmap_1(sK2,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(sK2,X1,X2,X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(sK2,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(sK2,X1,X2,X3,X4)) )
                      & m1_pre_topc(X3,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),sK5,sK3)
      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6)) )
    & m1_pre_topc(sK5,sK4)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v5_pre_topc(sK6,sK4,sK3)
    & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f21,f32,f31,f30,f29,f28])).

fof(f57,plain,(
    v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f46,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
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
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
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
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
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
    inference(flattening,[],[f18])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | ~ m1_pre_topc(X3,X2)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
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
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
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
    inference(equality_resolution,[],[f44])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X1,X0)
      | ~ r1_tmap_1(X1,X0,X2,sK1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f45,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f35,plain,(
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
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
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
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
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
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,(
    m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X1,X0)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ? [X4] :
                        ( X3 = X4
                        & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X2)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
                  ( ? [X4] :
                      ( X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X2)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f22,plain,(
    ! [X3,X2] :
      ( ? [X4] :
          ( X3 = X4
          & m1_subset_1(X4,u1_struct_0(X2)) )
     => ( sK0(X2,X3) = X3
        & m1_subset_1(sK0(X2,X3),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( sK0(X2,X3) = X3
                    & m1_subset_1(sK0(X2,X3),u1_struct_0(X2)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f22])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( sK0(X2,X3) = X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK0(X2,X3),u1_struct_0(X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_9,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ v5_pre_topc(X2,X0,X1)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_14,negated_conjecture,
    ( v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_386,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | sK6 != X2
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_387,plain,
    ( r1_tmap_1(sK4,sK3,sK6,X0)
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_15,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_391,plain,
    ( ~ v2_pre_topc(sK4)
    | r1_tmap_1(sK4,sK3,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_23,c_22,c_21,c_20,c_16,c_15,c_13])).

cnf(c_392,plain,
    ( r1_tmap_1(sK4,sK3,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(renaming,[status(thm)],[c_391])).

cnf(c_487,plain,
    ( r1_tmap_1(sK4,sK3,sK6,X0_48)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subtyping,[status(esa)],[c_392])).

cnf(c_513,plain,
    ( r1_tmap_1(sK4,sK3,sK6,X0_48)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_487])).

cnf(c_1108,plain,
    ( r1_tmap_1(sK4,sK3,sK6,X0_48) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_28,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_29,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_34,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_514,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_487])).

cnf(c_594,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_595,plain,
    ( r1_tmap_1(sK4,sK3,sK6,X0_48) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_498,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1096,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_498])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_512,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ l1_pre_topc(X1_50)
    | ~ v2_pre_topc(X1_50)
    | v2_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1082,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_1646,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK4) = iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1096,c_1082])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_508,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ l1_pre_topc(X1_50)
    | l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1471,plain,
    ( ~ m1_pre_topc(sK4,X0_50)
    | ~ l1_pre_topc(X0_50)
    | l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_508])).

cnf(c_1831,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1471])).

cnf(c_1832,plain,
    ( m1_pre_topc(sK4,sK2) != iProver_top
    | l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1831])).

cnf(c_1900,plain,
    ( m1_subset_1(X0_48,u1_struct_0(sK4)) != iProver_top
    | r1_tmap_1(sK4,sK3,sK6,X0_48) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1108,c_28,c_29,c_34,c_594,c_595,c_1646,c_1832])).

cnf(c_1901,plain,
    ( r1_tmap_1(sK4,sK3,sK6,X0_48) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1900])).

cnf(c_10,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_505,plain,
    ( ~ r1_tmap_1(X0_50,X1_50,X0_48,X1_48)
    | r1_tmap_1(X2_50,X1_50,k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_48),X1_48)
    | ~ v1_funct_2(X0_48,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ m1_subset_1(X1_48,u1_struct_0(X0_50))
    | ~ m1_subset_1(X1_48,u1_struct_0(X2_50))
    | ~ m1_pre_topc(X2_50,X3_50)
    | ~ m1_pre_topc(X0_50,X3_50)
    | ~ m1_pre_topc(X2_50,X0_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X3_50)
    | v2_struct_0(X2_50)
    | ~ v1_funct_1(X0_48)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X3_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X3_50) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1089,plain,
    ( r1_tmap_1(X0_50,X1_50,X0_48,X1_48) != iProver_top
    | r1_tmap_1(X2_50,X1_50,k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_48),X1_48) = iProver_top
    | v1_funct_2(X0_48,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(X2_50)) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X2_50,X3_50) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X3_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X3_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_7,plain,
    ( ~ r1_tmap_1(X0,X1,X2,sK1(X1,X0,X2))
    | v5_pre_topc(X2,X0,X1)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_11,negated_conjecture,
    ( ~ v5_pre_topc(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_360,plain,
    ( ~ r1_tmap_1(X0,X1,X2,sK1(X1,X0,X2))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | k3_tmap_1(sK2,sK3,sK4,sK5,sK6) != X2
    | sK5 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_11])).

cnf(c_361,plain,
    ( ~ r1_tmap_1(sK5,sK3,k3_tmap_1(sK2,sK3,sK4,sK5,sK6),sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6))
    | ~ l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_363,plain,
    ( ~ v2_pre_topc(sK5)
    | ~ r1_tmap_1(sK5,sK3,k3_tmap_1(sK2,sK3,sK4,sK5,sK6),sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6))
    | ~ l1_pre_topc(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_361,c_23,c_22,c_21,c_18])).

cnf(c_364,plain,
    ( ~ r1_tmap_1(sK5,sK3,k3_tmap_1(sK2,sK3,sK4,sK5,sK6),sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(renaming,[status(thm)],[c_363])).

cnf(c_488,plain,
    ( ~ r1_tmap_1(sK5,sK3,k3_tmap_1(sK2,sK3,sK4,sK5,sK6),sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(subtyping,[status(esa)],[c_364])).

cnf(c_1106,plain,
    ( r1_tmap_1(sK5,sK3,k3_tmap_1(sK2,sK3,sK4,sK5,sK6),sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6)) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_27,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_30,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_31,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_32,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_36,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_37,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_38,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_40,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_365,plain,
    ( r1_tmap_1(sK5,sK3,k3_tmap_1(sK2,sK3,sK4,sK5,sK6),sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6)) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_500,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1094,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_1629,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK5) = iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1094,c_1082])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0))
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_509,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ m1_pre_topc(X2_50,X3_50)
    | ~ m1_pre_topc(X0_50,X3_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X3_50)
    | ~ v1_funct_1(X0_48)
    | v1_funct_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_48))
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X3_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X3_50) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1554,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ m1_pre_topc(X0_50,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(X1_50)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_48)
    | v1_funct_1(k3_tmap_1(sK2,X1_50,X0_50,sK5,X0_48))
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_509])).

cnf(c_1708,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(sK4),u1_struct_0(X0_50))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_50))))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(X0_50)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_48)
    | v1_funct_1(k3_tmap_1(sK2,X0_50,sK4,sK5,X0_48))
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1554])).

cnf(c_1709,plain,
    ( v1_funct_2(X0_48,u1_struct_0(sK4),u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_50)))) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_50,sK4,sK5,X0_48)) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1708])).

cnf(c_1711,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1709])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_510,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_48),u1_struct_0(X3_50),u1_struct_0(X1_50))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_pre_topc(X3_50,X2_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X2_50)
    | ~ v1_funct_1(X0_48)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1574,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(sK4),u1_struct_0(X0_50))
    | v1_funct_2(k3_tmap_1(sK2,X0_50,sK4,X1_50,X0_48),u1_struct_0(X1_50),u1_struct_0(X0_50))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_50))))
    | ~ m1_pre_topc(X1_50,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(X0_50)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_48)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_510])).

cnf(c_1753,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(sK4),u1_struct_0(X0_50))
    | v1_funct_2(k3_tmap_1(sK2,X0_50,sK4,sK5,X0_48),u1_struct_0(sK5),u1_struct_0(X0_50))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_50))))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(X0_50)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_48)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1574])).

cnf(c_1754,plain,
    ( v1_funct_2(X0_48,u1_struct_0(sK4),u1_struct_0(X0_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_50,sK4,sK5,X0_48),u1_struct_0(sK5),u1_struct_0(X0_50)) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_50)))) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1753])).

cnf(c_1756,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1754])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X3,X2,X1,X4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_511,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | m1_subset_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50))))
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_pre_topc(X3_50,X2_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X2_50)
    | ~ v1_funct_1(X0_48)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1589,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(sK4),u1_struct_0(X0_50))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_50))))
    | m1_subset_1(k3_tmap_1(sK2,X0_50,sK4,X1_50,X0_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50))))
    | ~ m1_pre_topc(X1_50,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(X0_50)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_48)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_1775,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(sK4),u1_struct_0(X0_50))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_50))))
    | m1_subset_1(k3_tmap_1(sK2,X0_50,sK4,sK5,X0_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_50))))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(X0_50)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_48)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1589])).

cnf(c_1776,plain,
    ( v1_funct_2(X0_48,u1_struct_0(sK4),u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_50)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_50,sK4,sK5,X0_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_50)))) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1775])).

cnf(c_1778,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1776])).

cnf(c_1466,plain,
    ( ~ m1_pre_topc(sK5,X0_50)
    | ~ l1_pre_topc(X0_50)
    | l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_508])).

cnf(c_1828,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1466])).

cnf(c_1829,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | l1_pre_topc(sK5) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1828])).

cnf(c_2259,plain,
    ( r1_tmap_1(sK5,sK3,k3_tmap_1(sK2,sK3,sK4,sK5,sK6),sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1106,c_27,c_28,c_29,c_30,c_31,c_32,c_34,c_36,c_37,c_38,c_40,c_365,c_1629,c_1711,c_1756,c_1778,c_1829])).

cnf(c_2616,plain,
    ( r1_tmap_1(sK4,sK3,sK6,sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6)),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6)),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK5,sK4) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1089,c_2259])).

cnf(c_33,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_35,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12,negated_conjecture,
    ( m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_41,plain,
    ( m1_pre_topc(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK1(X2,X1,X0),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_410,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | m1_subset_1(sK1(X2,X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k3_tmap_1(sK2,sK3,sK4,sK5,sK6) != X0
    | sK5 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_11])).

cnf(c_411,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | m1_subset_1(sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6)),u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6))
    | ~ l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_413,plain,
    ( ~ v2_pre_topc(sK5)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | m1_subset_1(sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6)),u1_struct_0(sK5))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6))
    | ~ l1_pre_topc(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_411,c_23,c_22,c_21,c_18])).

cnf(c_414,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | m1_subset_1(sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6)),u1_struct_0(sK5))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(renaming,[status(thm)],[c_413])).

cnf(c_415,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6)),u1_struct_0(sK5)) = iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6)) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_414])).

cnf(c_486,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | m1_subset_1(sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6)),u1_struct_0(sK5))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(subtyping,[status(esa)],[c_414])).

cnf(c_1109,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6)),u1_struct_0(sK5)) = iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6)) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_1909,plain,
    ( m1_subset_1(sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6)),u1_struct_0(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1109,c_27,c_28,c_29,c_30,c_31,c_32,c_34,c_36,c_37,c_38,c_40,c_415,c_1629,c_1711,c_1756,c_1778,c_1829])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | sK0(X3,X0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_507,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(X0_50))
    | ~ m1_pre_topc(X1_50,X2_50)
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_pre_topc(X0_50,X1_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X2_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v2_pre_topc(X2_50)
    | sK0(X1_50,X0_48) = X0_48 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1087,plain,
    ( sK0(X0_50,X0_48) = X0_48
    | m1_subset_1(X0_48,u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | m1_pre_topc(X1_50,X2_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_2048,plain,
    ( sK0(X0_50,sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))) = sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK5,X0_50) != iProver_top
    | m1_pre_topc(sK5,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1909,c_1087])).

cnf(c_3133,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | m1_pre_topc(sK5,X1_50) != iProver_top
    | m1_pre_topc(sK5,X0_50) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | sK0(X0_50,sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))) = sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2048,c_35])).

cnf(c_3134,plain,
    ( sK0(X0_50,sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))) = sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK5,X0_50) != iProver_top
    | m1_pre_topc(sK5,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_3133])).

cnf(c_3149,plain,
    ( sK0(sK4,sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))) = sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))
    | m1_pre_topc(sK5,sK4) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1096,c_3134])).

cnf(c_1643,plain,
    ( ~ l1_pre_topc(sK2)
    | v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1629])).

cnf(c_1710,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1708])).

cnf(c_1755,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1753])).

cnf(c_1777,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1775])).

cnf(c_1544,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(X0_50))
    | ~ m1_pre_topc(X0_50,sK4)
    | ~ m1_pre_topc(X0_50,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(X0_50)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | sK0(sK4,X0_48) = X0_48 ),
    inference(instantiation,[status(thm)],[c_507])).

cnf(c_1692,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK5))
    | ~ m1_pre_topc(sK5,sK4)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | sK0(sK4,X0_48) = X0_48 ),
    inference(instantiation,[status(thm)],[c_1544])).

cnf(c_1931,plain,
    ( ~ m1_subset_1(sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6)),u1_struct_0(sK5))
    | ~ m1_pre_topc(sK5,sK4)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | sK0(sK4,sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))) = sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1692])).

cnf(c_3259,plain,
    ( sK0(sK4,sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))) = sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3149,c_26,c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_18,c_17,c_16,c_15,c_13,c_12,c_414,c_1643,c_1710,c_1755,c_1777,c_1828,c_1931])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK0(X2,X0),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_506,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(X0_50))
    | m1_subset_1(sK0(X1_50,X0_48),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X1_50,X2_50)
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_pre_topc(X0_50,X1_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X2_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v2_pre_topc(X2_50) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1088,plain,
    ( m1_subset_1(X0_48,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(sK0(X1_50,X0_48),u1_struct_0(X1_50)) = iProver_top
    | m1_pre_topc(X1_50,X2_50) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_2063,plain,
    ( m1_subset_1(sK0(X0_50,sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))),u1_struct_0(X0_50)) = iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK5,X0_50) != iProver_top
    | m1_pre_topc(sK5,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1909,c_1088])).

cnf(c_2437,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | m1_pre_topc(sK5,X1_50) != iProver_top
    | m1_pre_topc(sK5,X0_50) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_subset_1(sK0(X0_50,sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))),u1_struct_0(X0_50)) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2063,c_35])).

cnf(c_2438,plain,
    ( m1_subset_1(sK0(X0_50,sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))),u1_struct_0(X0_50)) = iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK5,X0_50) != iProver_top
    | m1_pre_topc(sK5,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_2437])).

cnf(c_2453,plain,
    ( m1_subset_1(sK0(sK4,sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))),u1_struct_0(sK4)) = iProver_top
    | m1_pre_topc(sK5,sK4) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1096,c_2438])).

cnf(c_1529,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(X0_50))
    | m1_subset_1(sK0(sK4,X0_48),u1_struct_0(sK4))
    | ~ m1_pre_topc(X0_50,sK4)
    | ~ m1_pre_topc(X0_50,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(X0_50)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_506])).

cnf(c_1685,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK5))
    | m1_subset_1(sK0(sK4,X0_48),u1_struct_0(sK4))
    | ~ m1_pre_topc(sK5,sK4)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(c_1932,plain,
    ( ~ m1_subset_1(sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6)),u1_struct_0(sK5))
    | m1_subset_1(sK0(sK4,sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))),u1_struct_0(sK4))
    | ~ m1_pre_topc(sK5,sK4)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1685])).

cnf(c_1933,plain,
    ( m1_subset_1(sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6)),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK0(sK4,sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))),u1_struct_0(sK4)) = iProver_top
    | m1_pre_topc(sK5,sK4) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1932])).

cnf(c_2732,plain,
    ( m1_subset_1(sK0(sK4,sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))),u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2453,c_27,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_40,c_41,c_415,c_1629,c_1711,c_1756,c_1778,c_1829,c_1933])).

cnf(c_3265,plain,
    ( m1_subset_1(sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6)),u1_struct_0(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3259,c_2732])).

cnf(c_6361,plain,
    ( r1_tmap_1(sK4,sK3,sK6,sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2616,c_27,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_40,c_41,c_415,c_1629,c_1711,c_1756,c_1778,c_1829,c_3265])).

cnf(c_6366,plain,
    ( m1_subset_1(sK1(sK3,sK5,k3_tmap_1(sK2,sK3,sK4,sK5,sK6)),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1901,c_6361])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6366,c_3265])).


%------------------------------------------------------------------------------
