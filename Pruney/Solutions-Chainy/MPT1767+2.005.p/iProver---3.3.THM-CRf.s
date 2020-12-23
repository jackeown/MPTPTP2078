%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:59 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 262 expanded)
%              Number of clauses        :   50 (  54 expanded)
%              Number of leaves         :   11 ( 105 expanded)
%              Depth                    :   11
%              Number of atoms          :  617 (3256 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal clause size      :   30 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

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
    inference(ennf_transformation,[],[f7])).

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

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f26])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
          & m1_pre_topc(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,sK5,X3)),k2_tmap_1(X0,X1,sK5,X2))
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
              & m1_pre_topc(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,k2_tmap_1(X0,X1,X4,sK4)),k2_tmap_1(X0,X1,X4,X2))
            & m1_pre_topc(X2,sK4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,sK3))
                & m1_pre_topc(sK3,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,k2_tmap_1(X0,sK2,X4,X3)),k2_tmap_1(X0,sK2,X4,X2))
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK2))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                        & m1_pre_topc(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,k2_tmap_1(sK1,X1,X4,X3)),k2_tmap_1(sK1,X1,X4,X2))
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,k2_tmap_1(sK1,sK2,sK5,sK4)),k2_tmap_1(sK1,sK2,sK5,sK3))
    & m1_pre_topc(sK3,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK1)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f27,f34,f33,f32,f31,f30])).

fof(f58,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( m1_pre_topc(X3,X2)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) )
                           => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
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
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
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
    inference(flattening,[],[f24])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
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
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,k2_tmap_1(sK1,sK2,sK5,sK4)),k2_tmap_1(sK1,sK2,sK5,sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f50,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_5,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_316,plain,
    ( r2_funct_2(X0_51,X1_51,X0_50,X0_50)
    | ~ v1_funct_2(X1_50,X0_51,X1_51)
    | ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1240,plain,
    ( r2_funct_2(u1_struct_0(X0_49),u1_struct_0(sK2),X0_50,X0_50)
    | ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK2,sK5,X0_49),u1_struct_0(X0_49),u1_struct_0(sK2))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK2))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK2,sK5,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK2))))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK5,X0_49)) ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_2653,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK4),k2_tmap_1(sK1,sK2,sK5,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_1240])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_312,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | m1_subset_1(k2_tmap_1(X0_49,X1_49,X0_50,X2_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_49),u1_struct_0(X1_49))))
    | ~ l1_struct_0(X2_49)
    | ~ l1_struct_0(X1_49)
    | ~ l1_struct_0(X0_49)
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1139,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
    | m1_subset_1(k2_tmap_1(sK1,sK2,sK5,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ l1_struct_0(X0_49)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_312])).

cnf(c_2020,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
    | m1_subset_1(k2_tmap_1(sK1,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1139])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_310,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | ~ l1_struct_0(X2_49)
    | ~ l1_struct_0(X1_49)
    | ~ l1_struct_0(X0_49)
    | ~ v1_funct_1(X0_50)
    | v1_funct_1(k2_tmap_1(X0_49,X1_49,X0_50,X2_49)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1117,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ l1_struct_0(X0_49)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK1,sK2,sK5,X0_49))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_310])).

cnf(c_1917,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK1,sK2,sK5,sK4))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1117])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_315,plain,
    ( ~ l1_pre_topc(X0_49)
    | l1_struct_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1840,plain,
    ( ~ l1_pre_topc(sK4)
    | l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_303,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_825,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_303])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_314,plain,
    ( ~ m1_pre_topc(X0_49,X1_49)
    | ~ l1_pre_topc(X1_49)
    | l1_pre_topc(X0_49) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_814,plain,
    ( m1_pre_topc(X0_49,X1_49) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_1706,plain,
    ( l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_825,c_814])).

cnf(c_1721,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1706])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_311,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | v1_funct_2(k2_tmap_1(X0_49,X1_49,X0_50,X2_49),u1_struct_0(X2_49),u1_struct_0(X1_49))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | ~ l1_struct_0(X2_49)
    | ~ l1_struct_0(X1_49)
    | ~ l1_struct_0(X0_49)
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1132,plain,
    ( v1_funct_2(k2_tmap_1(sK1,sK2,sK5,X0_49),u1_struct_0(X0_49),u1_struct_0(sK2))
    | ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ l1_struct_0(X0_49)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_1498,plain,
    ( v1_funct_2(k2_tmap_1(sK1,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1132])).

cnf(c_12,plain,
    ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_tmap_1(X3,X1,X4,X0))
    | r2_funct_2(u1_struct_0(X5),u1_struct_0(X1),k3_tmap_1(X3,X1,X0,X5,X2),k2_tmap_1(X3,X1,X4,X5))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_pre_topc(X5,X3)
    | ~ m1_pre_topc(X5,X0)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_309,plain,
    ( ~ r2_funct_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50,k2_tmap_1(X2_49,X1_49,X1_50,X0_49))
    | r2_funct_2(u1_struct_0(X3_49),u1_struct_0(X1_49),k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50),k2_tmap_1(X2_49,X1_49,X1_50,X3_49))
    | ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ v1_funct_2(X1_50,u1_struct_0(X2_49),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X3_49,X2_49)
    | ~ m1_pre_topc(X3_49,X0_49)
    | ~ m1_pre_topc(X0_49,X2_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_49),u1_struct_0(X1_49))))
    | v2_struct_0(X3_49)
    | v2_struct_0(X1_49)
    | v2_struct_0(X0_49)
    | v2_struct_0(X2_49)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(X2_49)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(X2_49)
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1179,plain,
    ( ~ r2_funct_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50,k2_tmap_1(sK1,X1_49,X1_50,X0_49))
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1_49),k3_tmap_1(sK1,X1_49,X0_49,sK3,X0_50),k2_tmap_1(sK1,X1_49,X1_50,sK3))
    | ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ v1_funct_2(X1_50,u1_struct_0(sK1),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X0_49,sK1)
    | ~ m1_pre_topc(sK3,X0_49)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1_49))))
    | v2_struct_0(X1_49)
    | v2_struct_0(X0_49)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_1318,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_49),X0_50,k2_tmap_1(sK1,X0_49,X1_50,sK4))
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0_49),k3_tmap_1(sK1,X0_49,sK4,sK3,X0_50),k2_tmap_1(sK1,X0_49,X1_50,sK3))
    | ~ v1_funct_2(X0_50,u1_struct_0(sK4),u1_struct_0(X0_49))
    | ~ v1_funct_2(X1_50,u1_struct_0(sK1),u1_struct_0(X0_49))
    | ~ m1_pre_topc(sK4,sK1)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_49))))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_49))))
    | v2_struct_0(X0_49)
    | v2_struct_0(sK4)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50) ),
    inference(instantiation,[status(thm)],[c_1179])).

cnf(c_1497,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK4),k2_tmap_1(sK1,sK2,X0_50,sK4))
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,k2_tmap_1(sK1,sK2,sK5,sK4)),k2_tmap_1(sK1,sK2,X0_50,sK3))
    | ~ v1_funct_2(X0_50,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK4,sK1)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | v2_struct_0(sK4)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_1318])).

cnf(c_1500,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK4),k2_tmap_1(sK1,sK2,sK5,sK4))
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,k2_tmap_1(sK1,sK2,sK5,sK4)),k2_tmap_1(sK1,sK2,sK5,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK4,sK1)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK1,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | v2_struct_0(sK4)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK5,sK4))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1497])).

cnf(c_1291,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_60,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_13,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,k2_tmap_1(sK1,sK2,sK5,sK4)),k2_tmap_1(sK1,sK2,sK5,sK3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_14,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_16,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2653,c_2020,c_1917,c_1840,c_1721,c_1498,c_1500,c_1291,c_60,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:57:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.89/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/0.98  
% 2.89/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.89/0.98  
% 2.89/0.98  ------  iProver source info
% 2.89/0.98  
% 2.89/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.89/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.89/0.98  git: non_committed_changes: false
% 2.89/0.98  git: last_make_outside_of_git: false
% 2.89/0.98  
% 2.89/0.98  ------ 
% 2.89/0.98  
% 2.89/0.98  ------ Input Options
% 2.89/0.98  
% 2.89/0.98  --out_options                           all
% 2.89/0.98  --tptp_safe_out                         true
% 2.89/0.98  --problem_path                          ""
% 2.89/0.98  --include_path                          ""
% 2.89/0.98  --clausifier                            res/vclausify_rel
% 2.89/0.98  --clausifier_options                    --mode clausify
% 2.89/0.98  --stdin                                 false
% 2.89/0.98  --stats_out                             all
% 2.89/0.98  
% 2.89/0.98  ------ General Options
% 2.89/0.98  
% 2.89/0.98  --fof                                   false
% 2.89/0.98  --time_out_real                         305.
% 2.89/0.98  --time_out_virtual                      -1.
% 2.89/0.98  --symbol_type_check                     false
% 2.89/0.98  --clausify_out                          false
% 2.89/0.98  --sig_cnt_out                           false
% 2.89/0.98  --trig_cnt_out                          false
% 2.89/0.98  --trig_cnt_out_tolerance                1.
% 2.89/0.98  --trig_cnt_out_sk_spl                   false
% 2.89/0.98  --abstr_cl_out                          false
% 2.89/0.98  
% 2.89/0.98  ------ Global Options
% 2.89/0.98  
% 2.89/0.98  --schedule                              default
% 2.89/0.98  --add_important_lit                     false
% 2.89/0.98  --prop_solver_per_cl                    1000
% 2.89/0.98  --min_unsat_core                        false
% 2.89/0.98  --soft_assumptions                      false
% 2.89/0.98  --soft_lemma_size                       3
% 2.89/0.98  --prop_impl_unit_size                   0
% 2.89/0.98  --prop_impl_unit                        []
% 2.89/0.98  --share_sel_clauses                     true
% 2.89/0.98  --reset_solvers                         false
% 2.89/0.98  --bc_imp_inh                            [conj_cone]
% 2.89/0.98  --conj_cone_tolerance                   3.
% 2.89/0.98  --extra_neg_conj                        none
% 2.89/0.98  --large_theory_mode                     true
% 2.89/0.98  --prolific_symb_bound                   200
% 2.89/0.98  --lt_threshold                          2000
% 2.89/0.98  --clause_weak_htbl                      true
% 2.89/0.98  --gc_record_bc_elim                     false
% 2.89/0.98  
% 2.89/0.98  ------ Preprocessing Options
% 2.89/0.98  
% 2.89/0.98  --preprocessing_flag                    true
% 2.89/0.98  --time_out_prep_mult                    0.1
% 2.89/0.98  --splitting_mode                        input
% 2.89/0.98  --splitting_grd                         true
% 2.89/0.98  --splitting_cvd                         false
% 2.89/0.98  --splitting_cvd_svl                     false
% 2.89/0.98  --splitting_nvd                         32
% 2.89/0.98  --sub_typing                            true
% 2.89/0.98  --prep_gs_sim                           true
% 2.89/0.98  --prep_unflatten                        true
% 2.89/0.98  --prep_res_sim                          true
% 2.89/0.98  --prep_upred                            true
% 2.89/0.98  --prep_sem_filter                       exhaustive
% 2.89/0.98  --prep_sem_filter_out                   false
% 2.89/0.98  --pred_elim                             true
% 2.89/0.98  --res_sim_input                         true
% 2.89/0.98  --eq_ax_congr_red                       true
% 2.89/0.98  --pure_diseq_elim                       true
% 2.89/0.98  --brand_transform                       false
% 2.89/0.98  --non_eq_to_eq                          false
% 2.89/0.98  --prep_def_merge                        true
% 2.89/0.98  --prep_def_merge_prop_impl              false
% 2.89/0.98  --prep_def_merge_mbd                    true
% 2.89/0.98  --prep_def_merge_tr_red                 false
% 2.89/0.98  --prep_def_merge_tr_cl                  false
% 2.89/0.98  --smt_preprocessing                     true
% 2.89/0.98  --smt_ac_axioms                         fast
% 2.89/0.98  --preprocessed_out                      false
% 2.89/0.98  --preprocessed_stats                    false
% 2.89/0.98  
% 2.89/0.98  ------ Abstraction refinement Options
% 2.89/0.98  
% 2.89/0.98  --abstr_ref                             []
% 2.89/0.98  --abstr_ref_prep                        false
% 2.89/0.98  --abstr_ref_until_sat                   false
% 2.89/0.98  --abstr_ref_sig_restrict                funpre
% 2.89/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/0.98  --abstr_ref_under                       []
% 2.89/0.98  
% 2.89/0.98  ------ SAT Options
% 2.89/0.98  
% 2.89/0.98  --sat_mode                              false
% 2.89/0.98  --sat_fm_restart_options                ""
% 2.89/0.98  --sat_gr_def                            false
% 2.89/0.98  --sat_epr_types                         true
% 2.89/0.98  --sat_non_cyclic_types                  false
% 2.89/0.98  --sat_finite_models                     false
% 2.89/0.98  --sat_fm_lemmas                         false
% 2.89/0.98  --sat_fm_prep                           false
% 2.89/0.98  --sat_fm_uc_incr                        true
% 2.89/0.98  --sat_out_model                         small
% 2.89/0.98  --sat_out_clauses                       false
% 2.89/0.98  
% 2.89/0.98  ------ QBF Options
% 2.89/0.98  
% 2.89/0.98  --qbf_mode                              false
% 2.89/0.98  --qbf_elim_univ                         false
% 2.89/0.98  --qbf_dom_inst                          none
% 2.89/0.98  --qbf_dom_pre_inst                      false
% 2.89/0.98  --qbf_sk_in                             false
% 2.89/0.98  --qbf_pred_elim                         true
% 2.89/0.98  --qbf_split                             512
% 2.89/0.98  
% 2.89/0.98  ------ BMC1 Options
% 2.89/0.98  
% 2.89/0.98  --bmc1_incremental                      false
% 2.89/0.98  --bmc1_axioms                           reachable_all
% 2.89/0.98  --bmc1_min_bound                        0
% 2.89/0.98  --bmc1_max_bound                        -1
% 2.89/0.98  --bmc1_max_bound_default                -1
% 2.89/0.98  --bmc1_symbol_reachability              true
% 2.89/0.98  --bmc1_property_lemmas                  false
% 2.89/0.98  --bmc1_k_induction                      false
% 2.89/0.98  --bmc1_non_equiv_states                 false
% 2.89/0.98  --bmc1_deadlock                         false
% 2.89/0.98  --bmc1_ucm                              false
% 2.89/0.98  --bmc1_add_unsat_core                   none
% 2.89/0.98  --bmc1_unsat_core_children              false
% 2.89/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/0.98  --bmc1_out_stat                         full
% 2.89/0.98  --bmc1_ground_init                      false
% 2.89/0.98  --bmc1_pre_inst_next_state              false
% 2.89/0.98  --bmc1_pre_inst_state                   false
% 2.89/0.98  --bmc1_pre_inst_reach_state             false
% 2.89/0.98  --bmc1_out_unsat_core                   false
% 2.89/0.98  --bmc1_aig_witness_out                  false
% 2.89/0.98  --bmc1_verbose                          false
% 2.89/0.98  --bmc1_dump_clauses_tptp                false
% 2.89/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.89/0.98  --bmc1_dump_file                        -
% 2.89/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.89/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.89/0.98  --bmc1_ucm_extend_mode                  1
% 2.89/0.98  --bmc1_ucm_init_mode                    2
% 2.89/0.98  --bmc1_ucm_cone_mode                    none
% 2.89/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.89/0.98  --bmc1_ucm_relax_model                  4
% 2.89/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.89/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/0.98  --bmc1_ucm_layered_model                none
% 2.89/0.98  --bmc1_ucm_max_lemma_size               10
% 2.89/0.98  
% 2.89/0.98  ------ AIG Options
% 2.89/0.98  
% 2.89/0.98  --aig_mode                              false
% 2.89/0.98  
% 2.89/0.98  ------ Instantiation Options
% 2.89/0.98  
% 2.89/0.98  --instantiation_flag                    true
% 2.89/0.98  --inst_sos_flag                         false
% 2.89/0.98  --inst_sos_phase                        true
% 2.89/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/0.98  --inst_lit_sel_side                     num_symb
% 2.89/0.98  --inst_solver_per_active                1400
% 2.89/0.98  --inst_solver_calls_frac                1.
% 2.89/0.98  --inst_passive_queue_type               priority_queues
% 2.89/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/0.98  --inst_passive_queues_freq              [25;2]
% 2.89/0.98  --inst_dismatching                      true
% 2.89/0.98  --inst_eager_unprocessed_to_passive     true
% 2.89/0.98  --inst_prop_sim_given                   true
% 2.89/0.98  --inst_prop_sim_new                     false
% 2.89/0.98  --inst_subs_new                         false
% 2.89/0.98  --inst_eq_res_simp                      false
% 2.89/0.98  --inst_subs_given                       false
% 2.89/0.98  --inst_orphan_elimination               true
% 2.89/0.98  --inst_learning_loop_flag               true
% 2.89/0.98  --inst_learning_start                   3000
% 2.89/0.98  --inst_learning_factor                  2
% 2.89/0.98  --inst_start_prop_sim_after_learn       3
% 2.89/0.98  --inst_sel_renew                        solver
% 2.89/0.98  --inst_lit_activity_flag                true
% 2.89/0.98  --inst_restr_to_given                   false
% 2.89/0.98  --inst_activity_threshold               500
% 2.89/0.98  --inst_out_proof                        true
% 2.89/0.98  
% 2.89/0.98  ------ Resolution Options
% 2.89/0.98  
% 2.89/0.98  --resolution_flag                       true
% 2.89/0.98  --res_lit_sel                           adaptive
% 2.89/0.98  --res_lit_sel_side                      none
% 2.89/0.98  --res_ordering                          kbo
% 2.89/0.98  --res_to_prop_solver                    active
% 2.89/0.98  --res_prop_simpl_new                    false
% 2.89/0.98  --res_prop_simpl_given                  true
% 2.89/0.98  --res_passive_queue_type                priority_queues
% 2.89/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/0.98  --res_passive_queues_freq               [15;5]
% 2.89/0.98  --res_forward_subs                      full
% 2.89/0.98  --res_backward_subs                     full
% 2.89/0.98  --res_forward_subs_resolution           true
% 2.89/0.98  --res_backward_subs_resolution          true
% 2.89/0.98  --res_orphan_elimination                true
% 2.89/0.98  --res_time_limit                        2.
% 2.89/0.98  --res_out_proof                         true
% 2.89/0.98  
% 2.89/0.98  ------ Superposition Options
% 2.89/0.98  
% 2.89/0.98  --superposition_flag                    true
% 2.89/0.98  --sup_passive_queue_type                priority_queues
% 2.89/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.89/0.98  --demod_completeness_check              fast
% 2.89/0.98  --demod_use_ground                      true
% 2.89/0.98  --sup_to_prop_solver                    passive
% 2.89/0.98  --sup_prop_simpl_new                    true
% 2.89/0.98  --sup_prop_simpl_given                  true
% 2.89/0.98  --sup_fun_splitting                     false
% 2.89/0.98  --sup_smt_interval                      50000
% 2.89/0.98  
% 2.89/0.98  ------ Superposition Simplification Setup
% 2.89/0.98  
% 2.89/0.98  --sup_indices_passive                   []
% 2.89/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.98  --sup_full_bw                           [BwDemod]
% 2.89/0.98  --sup_immed_triv                        [TrivRules]
% 2.89/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.98  --sup_immed_bw_main                     []
% 2.89/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.98  
% 2.89/0.98  ------ Combination Options
% 2.89/0.98  
% 2.89/0.98  --comb_res_mult                         3
% 2.89/0.98  --comb_sup_mult                         2
% 2.89/0.98  --comb_inst_mult                        10
% 2.89/0.98  
% 2.89/0.98  ------ Debug Options
% 2.89/0.98  
% 2.89/0.98  --dbg_backtrace                         false
% 2.89/0.98  --dbg_dump_prop_clauses                 false
% 2.89/0.98  --dbg_dump_prop_clauses_file            -
% 2.89/0.98  --dbg_out_stat                          false
% 2.89/0.98  ------ Parsing...
% 2.89/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.89/0.98  
% 2.89/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.89/0.98  
% 2.89/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.89/0.98  
% 2.89/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.89/0.98  ------ Proving...
% 2.89/0.98  ------ Problem Properties 
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  clauses                                 28
% 2.89/0.98  conjectures                             15
% 2.89/0.98  EPR                                     14
% 2.89/0.98  Horn                                    26
% 2.89/0.98  unary                                   18
% 2.89/0.98  binary                                  1
% 2.89/0.98  lits                                    87
% 2.89/0.98  lits eq                                 1
% 2.89/0.98  fd_pure                                 0
% 2.89/0.98  fd_pseudo                               0
% 2.89/0.98  fd_cond                                 0
% 2.89/0.98  fd_pseudo_cond                          0
% 2.89/0.98  AC symbols                              0
% 2.89/0.98  
% 2.89/0.98  ------ Schedule dynamic 5 is on 
% 2.89/0.98  
% 2.89/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  ------ 
% 2.89/0.98  Current options:
% 2.89/0.98  ------ 
% 2.89/0.98  
% 2.89/0.98  ------ Input Options
% 2.89/0.98  
% 2.89/0.98  --out_options                           all
% 2.89/0.98  --tptp_safe_out                         true
% 2.89/0.98  --problem_path                          ""
% 2.89/0.98  --include_path                          ""
% 2.89/0.98  --clausifier                            res/vclausify_rel
% 2.89/0.98  --clausifier_options                    --mode clausify
% 2.89/0.98  --stdin                                 false
% 2.89/0.98  --stats_out                             all
% 2.89/0.98  
% 2.89/0.98  ------ General Options
% 2.89/0.98  
% 2.89/0.98  --fof                                   false
% 2.89/0.98  --time_out_real                         305.
% 2.89/0.98  --time_out_virtual                      -1.
% 2.89/0.98  --symbol_type_check                     false
% 2.89/0.98  --clausify_out                          false
% 2.89/0.98  --sig_cnt_out                           false
% 2.89/0.98  --trig_cnt_out                          false
% 2.89/0.98  --trig_cnt_out_tolerance                1.
% 2.89/0.98  --trig_cnt_out_sk_spl                   false
% 2.89/0.98  --abstr_cl_out                          false
% 2.89/0.98  
% 2.89/0.98  ------ Global Options
% 2.89/0.98  
% 2.89/0.98  --schedule                              default
% 2.89/0.98  --add_important_lit                     false
% 2.89/0.98  --prop_solver_per_cl                    1000
% 2.89/0.98  --min_unsat_core                        false
% 2.89/0.98  --soft_assumptions                      false
% 2.89/0.98  --soft_lemma_size                       3
% 2.89/0.98  --prop_impl_unit_size                   0
% 2.89/0.98  --prop_impl_unit                        []
% 2.89/0.98  --share_sel_clauses                     true
% 2.89/0.98  --reset_solvers                         false
% 2.89/0.98  --bc_imp_inh                            [conj_cone]
% 2.89/0.98  --conj_cone_tolerance                   3.
% 2.89/0.98  --extra_neg_conj                        none
% 2.89/0.98  --large_theory_mode                     true
% 2.89/0.98  --prolific_symb_bound                   200
% 2.89/0.98  --lt_threshold                          2000
% 2.89/0.98  --clause_weak_htbl                      true
% 2.89/0.98  --gc_record_bc_elim                     false
% 2.89/0.98  
% 2.89/0.98  ------ Preprocessing Options
% 2.89/0.98  
% 2.89/0.98  --preprocessing_flag                    true
% 2.89/0.98  --time_out_prep_mult                    0.1
% 2.89/0.98  --splitting_mode                        input
% 2.89/0.98  --splitting_grd                         true
% 2.89/0.98  --splitting_cvd                         false
% 2.89/0.98  --splitting_cvd_svl                     false
% 2.89/0.98  --splitting_nvd                         32
% 2.89/0.98  --sub_typing                            true
% 2.89/0.98  --prep_gs_sim                           true
% 2.89/0.98  --prep_unflatten                        true
% 2.89/0.98  --prep_res_sim                          true
% 2.89/0.98  --prep_upred                            true
% 2.89/0.98  --prep_sem_filter                       exhaustive
% 2.89/0.98  --prep_sem_filter_out                   false
% 2.89/0.98  --pred_elim                             true
% 2.89/0.98  --res_sim_input                         true
% 2.89/0.98  --eq_ax_congr_red                       true
% 2.89/0.98  --pure_diseq_elim                       true
% 2.89/0.98  --brand_transform                       false
% 2.89/0.98  --non_eq_to_eq                          false
% 2.89/0.98  --prep_def_merge                        true
% 2.89/0.98  --prep_def_merge_prop_impl              false
% 2.89/0.98  --prep_def_merge_mbd                    true
% 2.89/0.98  --prep_def_merge_tr_red                 false
% 2.89/0.98  --prep_def_merge_tr_cl                  false
% 2.89/0.98  --smt_preprocessing                     true
% 2.89/0.98  --smt_ac_axioms                         fast
% 2.89/0.98  --preprocessed_out                      false
% 2.89/0.98  --preprocessed_stats                    false
% 2.89/0.98  
% 2.89/0.98  ------ Abstraction refinement Options
% 2.89/0.98  
% 2.89/0.98  --abstr_ref                             []
% 2.89/0.98  --abstr_ref_prep                        false
% 2.89/0.98  --abstr_ref_until_sat                   false
% 2.89/0.98  --abstr_ref_sig_restrict                funpre
% 2.89/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/0.98  --abstr_ref_under                       []
% 2.89/0.98  
% 2.89/0.98  ------ SAT Options
% 2.89/0.98  
% 2.89/0.98  --sat_mode                              false
% 2.89/0.98  --sat_fm_restart_options                ""
% 2.89/0.98  --sat_gr_def                            false
% 2.89/0.98  --sat_epr_types                         true
% 2.89/0.98  --sat_non_cyclic_types                  false
% 2.89/0.98  --sat_finite_models                     false
% 2.89/0.98  --sat_fm_lemmas                         false
% 2.89/0.98  --sat_fm_prep                           false
% 2.89/0.98  --sat_fm_uc_incr                        true
% 2.89/0.98  --sat_out_model                         small
% 2.89/0.98  --sat_out_clauses                       false
% 2.89/0.98  
% 2.89/0.98  ------ QBF Options
% 2.89/0.98  
% 2.89/0.98  --qbf_mode                              false
% 2.89/0.98  --qbf_elim_univ                         false
% 2.89/0.98  --qbf_dom_inst                          none
% 2.89/0.98  --qbf_dom_pre_inst                      false
% 2.89/0.98  --qbf_sk_in                             false
% 2.89/0.98  --qbf_pred_elim                         true
% 2.89/0.98  --qbf_split                             512
% 2.89/0.98  
% 2.89/0.98  ------ BMC1 Options
% 2.89/0.98  
% 2.89/0.98  --bmc1_incremental                      false
% 2.89/0.98  --bmc1_axioms                           reachable_all
% 2.89/0.98  --bmc1_min_bound                        0
% 2.89/0.98  --bmc1_max_bound                        -1
% 2.89/0.98  --bmc1_max_bound_default                -1
% 2.89/0.98  --bmc1_symbol_reachability              true
% 2.89/0.98  --bmc1_property_lemmas                  false
% 2.89/0.98  --bmc1_k_induction                      false
% 2.89/0.98  --bmc1_non_equiv_states                 false
% 2.89/0.98  --bmc1_deadlock                         false
% 2.89/0.98  --bmc1_ucm                              false
% 2.89/0.98  --bmc1_add_unsat_core                   none
% 2.89/0.98  --bmc1_unsat_core_children              false
% 2.89/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/0.98  --bmc1_out_stat                         full
% 2.89/0.98  --bmc1_ground_init                      false
% 2.89/0.98  --bmc1_pre_inst_next_state              false
% 2.89/0.98  --bmc1_pre_inst_state                   false
% 2.89/0.98  --bmc1_pre_inst_reach_state             false
% 2.89/0.98  --bmc1_out_unsat_core                   false
% 2.89/0.98  --bmc1_aig_witness_out                  false
% 2.89/0.98  --bmc1_verbose                          false
% 2.89/0.98  --bmc1_dump_clauses_tptp                false
% 2.89/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.89/0.98  --bmc1_dump_file                        -
% 2.89/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.89/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.89/0.98  --bmc1_ucm_extend_mode                  1
% 2.89/0.98  --bmc1_ucm_init_mode                    2
% 2.89/0.98  --bmc1_ucm_cone_mode                    none
% 2.89/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.89/0.98  --bmc1_ucm_relax_model                  4
% 2.89/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.89/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/0.98  --bmc1_ucm_layered_model                none
% 2.89/0.98  --bmc1_ucm_max_lemma_size               10
% 2.89/0.98  
% 2.89/0.98  ------ AIG Options
% 2.89/0.98  
% 2.89/0.98  --aig_mode                              false
% 2.89/0.98  
% 2.89/0.98  ------ Instantiation Options
% 2.89/0.98  
% 2.89/0.98  --instantiation_flag                    true
% 2.89/0.98  --inst_sos_flag                         false
% 2.89/0.98  --inst_sos_phase                        true
% 2.89/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/0.98  --inst_lit_sel_side                     none
% 2.89/0.98  --inst_solver_per_active                1400
% 2.89/0.98  --inst_solver_calls_frac                1.
% 2.89/0.98  --inst_passive_queue_type               priority_queues
% 2.89/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/0.98  --inst_passive_queues_freq              [25;2]
% 2.89/0.98  --inst_dismatching                      true
% 2.89/0.98  --inst_eager_unprocessed_to_passive     true
% 2.89/0.98  --inst_prop_sim_given                   true
% 2.89/0.98  --inst_prop_sim_new                     false
% 2.89/0.98  --inst_subs_new                         false
% 2.89/0.98  --inst_eq_res_simp                      false
% 2.89/0.98  --inst_subs_given                       false
% 2.89/0.98  --inst_orphan_elimination               true
% 2.89/0.98  --inst_learning_loop_flag               true
% 2.89/0.98  --inst_learning_start                   3000
% 2.89/0.98  --inst_learning_factor                  2
% 2.89/0.98  --inst_start_prop_sim_after_learn       3
% 2.89/0.98  --inst_sel_renew                        solver
% 2.89/0.98  --inst_lit_activity_flag                true
% 2.89/0.98  --inst_restr_to_given                   false
% 2.89/0.98  --inst_activity_threshold               500
% 2.89/0.98  --inst_out_proof                        true
% 2.89/0.98  
% 2.89/0.98  ------ Resolution Options
% 2.89/0.98  
% 2.89/0.98  --resolution_flag                       false
% 2.89/0.98  --res_lit_sel                           adaptive
% 2.89/0.98  --res_lit_sel_side                      none
% 2.89/0.98  --res_ordering                          kbo
% 2.89/0.98  --res_to_prop_solver                    active
% 2.89/0.98  --res_prop_simpl_new                    false
% 2.89/0.98  --res_prop_simpl_given                  true
% 2.89/0.98  --res_passive_queue_type                priority_queues
% 2.89/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/0.98  --res_passive_queues_freq               [15;5]
% 2.89/0.98  --res_forward_subs                      full
% 2.89/0.98  --res_backward_subs                     full
% 2.89/0.98  --res_forward_subs_resolution           true
% 2.89/0.98  --res_backward_subs_resolution          true
% 2.89/0.98  --res_orphan_elimination                true
% 2.89/0.98  --res_time_limit                        2.
% 2.89/0.98  --res_out_proof                         true
% 2.89/0.98  
% 2.89/0.98  ------ Superposition Options
% 2.89/0.98  
% 2.89/0.98  --superposition_flag                    true
% 2.89/0.98  --sup_passive_queue_type                priority_queues
% 2.89/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.89/0.98  --demod_completeness_check              fast
% 2.89/0.98  --demod_use_ground                      true
% 2.89/0.98  --sup_to_prop_solver                    passive
% 2.89/0.98  --sup_prop_simpl_new                    true
% 2.89/0.98  --sup_prop_simpl_given                  true
% 2.89/0.98  --sup_fun_splitting                     false
% 2.89/0.98  --sup_smt_interval                      50000
% 2.89/0.98  
% 2.89/0.98  ------ Superposition Simplification Setup
% 2.89/0.98  
% 2.89/0.98  --sup_indices_passive                   []
% 2.89/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.98  --sup_full_bw                           [BwDemod]
% 2.89/0.98  --sup_immed_triv                        [TrivRules]
% 2.89/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.98  --sup_immed_bw_main                     []
% 2.89/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.98  
% 2.89/0.98  ------ Combination Options
% 2.89/0.98  
% 2.89/0.98  --comb_res_mult                         3
% 2.89/0.98  --comb_sup_mult                         2
% 2.89/0.98  --comb_inst_mult                        10
% 2.89/0.98  
% 2.89/0.98  ------ Debug Options
% 2.89/0.98  
% 2.89/0.98  --dbg_backtrace                         false
% 2.89/0.98  --dbg_dump_prop_clauses                 false
% 2.89/0.98  --dbg_dump_prop_clauses_file            -
% 2.89/0.98  --dbg_out_stat                          false
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  ------ Proving...
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  % SZS status Theorem for theBenchmark.p
% 2.89/0.98  
% 2.89/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.89/0.98  
% 2.89/0.98  fof(f3,axiom,(
% 2.89/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f16,plain,(
% 2.89/0.98    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.89/0.98    inference(ennf_transformation,[],[f3])).
% 2.89/0.98  
% 2.89/0.98  fof(f17,plain,(
% 2.89/0.98    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.89/0.98    inference(flattening,[],[f16])).
% 2.89/0.98  
% 2.89/0.98  fof(f41,plain,(
% 2.89/0.98    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.89/0.98    inference(cnf_transformation,[],[f17])).
% 2.89/0.98  
% 2.89/0.98  fof(f7,axiom,(
% 2.89/0.98    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f22,plain,(
% 2.89/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 2.89/0.98    inference(ennf_transformation,[],[f7])).
% 2.89/0.98  
% 2.89/0.98  fof(f23,plain,(
% 2.89/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 2.89/0.98    inference(flattening,[],[f22])).
% 2.89/0.98  
% 2.89/0.98  fof(f47,plain,(
% 2.89/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.89/0.98    inference(cnf_transformation,[],[f23])).
% 2.89/0.98  
% 2.89/0.98  fof(f45,plain,(
% 2.89/0.98    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.89/0.98    inference(cnf_transformation,[],[f23])).
% 2.89/0.98  
% 2.89/0.98  fof(f4,axiom,(
% 2.89/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f18,plain,(
% 2.89/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.89/0.98    inference(ennf_transformation,[],[f4])).
% 2.89/0.98  
% 2.89/0.98  fof(f42,plain,(
% 2.89/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.89/0.98    inference(cnf_transformation,[],[f18])).
% 2.89/0.98  
% 2.89/0.98  fof(f9,conjecture,(
% 2.89/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f10,negated_conjecture,(
% 2.89/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 2.89/0.98    inference(negated_conjecture,[],[f9])).
% 2.89/0.98  
% 2.89/0.98  fof(f26,plain,(
% 2.89/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.89/0.98    inference(ennf_transformation,[],[f10])).
% 2.89/0.98  
% 2.89/0.98  fof(f27,plain,(
% 2.89/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.89/0.98    inference(flattening,[],[f26])).
% 2.89/0.98  
% 2.89/0.98  fof(f34,plain,(
% 2.89/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,sK5,X3)),k2_tmap_1(X0,X1,sK5,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 2.89/0.98    introduced(choice_axiom,[])).
% 2.89/0.98  
% 2.89/0.98  fof(f33,plain,(
% 2.89/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,k2_tmap_1(X0,X1,X4,sK4)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,sK4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.89/0.98    introduced(choice_axiom,[])).
% 2.89/0.98  
% 2.89/0.98  fof(f32,plain,(
% 2.89/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,sK3)) & m1_pre_topc(sK3,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.89/0.98    introduced(choice_axiom,[])).
% 2.89/0.98  
% 2.89/0.98  fof(f31,plain,(
% 2.89/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,k2_tmap_1(X0,sK2,X4,X3)),k2_tmap_1(X0,sK2,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.89/0.98    introduced(choice_axiom,[])).
% 2.89/0.98  
% 2.89/0.98  fof(f30,plain,(
% 2.89/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,k2_tmap_1(sK1,X1,X4,X3)),k2_tmap_1(sK1,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.89/0.98    introduced(choice_axiom,[])).
% 2.89/0.98  
% 2.89/0.98  fof(f35,plain,(
% 2.89/0.98    ((((~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,k2_tmap_1(sK1,sK2,sK5,sK4)),k2_tmap_1(sK1,sK2,sK5,sK3)) & m1_pre_topc(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.89/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f27,f34,f33,f32,f31,f30])).
% 2.89/0.98  
% 2.89/0.98  fof(f58,plain,(
% 2.89/0.98    m1_pre_topc(sK4,sK1)),
% 2.89/0.98    inference(cnf_transformation,[],[f35])).
% 2.89/0.98  
% 2.89/0.98  fof(f5,axiom,(
% 2.89/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f19,plain,(
% 2.89/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.89/0.98    inference(ennf_transformation,[],[f5])).
% 2.89/0.98  
% 2.89/0.98  fof(f43,plain,(
% 2.89/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.89/0.98    inference(cnf_transformation,[],[f19])).
% 2.89/0.98  
% 2.89/0.98  fof(f46,plain,(
% 2.89/0.98    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.89/0.98    inference(cnf_transformation,[],[f23])).
% 2.89/0.98  
% 2.89/0.98  fof(f8,axiom,(
% 2.89/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_pre_topc(X3,X2) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))) => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f24,plain,(
% 2.89/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | (~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.89/0.98    inference(ennf_transformation,[],[f8])).
% 2.89/0.98  
% 2.89/0.98  fof(f25,plain,(
% 2.89/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.89/0.98    inference(flattening,[],[f24])).
% 2.89/0.98  
% 2.89/0.98  fof(f48,plain,(
% 2.89/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.89/0.98    inference(cnf_transformation,[],[f25])).
% 2.89/0.98  
% 2.89/0.98  fof(f63,plain,(
% 2.89/0.98    ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,k2_tmap_1(sK1,sK2,sK5,sK4)),k2_tmap_1(sK1,sK2,sK5,sK3))),
% 2.89/0.98    inference(cnf_transformation,[],[f35])).
% 2.89/0.98  
% 2.89/0.98  fof(f62,plain,(
% 2.89/0.98    m1_pre_topc(sK3,sK4)),
% 2.89/0.98    inference(cnf_transformation,[],[f35])).
% 2.89/0.98  
% 2.89/0.98  fof(f61,plain,(
% 2.89/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 2.89/0.98    inference(cnf_transformation,[],[f35])).
% 2.89/0.98  
% 2.89/0.98  fof(f60,plain,(
% 2.89/0.98    v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))),
% 2.89/0.98    inference(cnf_transformation,[],[f35])).
% 2.89/0.98  
% 2.89/0.98  fof(f59,plain,(
% 2.89/0.98    v1_funct_1(sK5)),
% 2.89/0.98    inference(cnf_transformation,[],[f35])).
% 2.89/0.98  
% 2.89/0.98  fof(f57,plain,(
% 2.89/0.98    ~v2_struct_0(sK4)),
% 2.89/0.98    inference(cnf_transformation,[],[f35])).
% 2.89/0.98  
% 2.89/0.98  fof(f56,plain,(
% 2.89/0.98    m1_pre_topc(sK3,sK1)),
% 2.89/0.98    inference(cnf_transformation,[],[f35])).
% 2.89/0.98  
% 2.89/0.98  fof(f55,plain,(
% 2.89/0.98    ~v2_struct_0(sK3)),
% 2.89/0.98    inference(cnf_transformation,[],[f35])).
% 2.89/0.98  
% 2.89/0.98  fof(f54,plain,(
% 2.89/0.98    l1_pre_topc(sK2)),
% 2.89/0.98    inference(cnf_transformation,[],[f35])).
% 2.89/0.98  
% 2.89/0.98  fof(f53,plain,(
% 2.89/0.98    v2_pre_topc(sK2)),
% 2.89/0.98    inference(cnf_transformation,[],[f35])).
% 2.89/0.98  
% 2.89/0.98  fof(f52,plain,(
% 2.89/0.98    ~v2_struct_0(sK2)),
% 2.89/0.98    inference(cnf_transformation,[],[f35])).
% 2.89/0.98  
% 2.89/0.98  fof(f51,plain,(
% 2.89/0.98    l1_pre_topc(sK1)),
% 2.89/0.98    inference(cnf_transformation,[],[f35])).
% 2.89/0.98  
% 2.89/0.98  fof(f50,plain,(
% 2.89/0.98    v2_pre_topc(sK1)),
% 2.89/0.98    inference(cnf_transformation,[],[f35])).
% 2.89/0.98  
% 2.89/0.98  fof(f49,plain,(
% 2.89/0.98    ~v2_struct_0(sK1)),
% 2.89/0.98    inference(cnf_transformation,[],[f35])).
% 2.89/0.98  
% 2.89/0.98  cnf(c_5,plain,
% 2.89/0.98      ( r2_funct_2(X0,X1,X2,X2)
% 2.89/0.98      | ~ v1_funct_2(X3,X0,X1)
% 2.89/0.98      | ~ v1_funct_2(X2,X0,X1)
% 2.89/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.89/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.89/0.98      | ~ v1_funct_1(X2)
% 2.89/0.98      | ~ v1_funct_1(X3) ),
% 2.89/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_316,plain,
% 2.89/0.98      ( r2_funct_2(X0_51,X1_51,X0_50,X0_50)
% 2.89/0.98      | ~ v1_funct_2(X1_50,X0_51,X1_51)
% 2.89/0.98      | ~ v1_funct_2(X0_50,X0_51,X1_51)
% 2.89/0.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.89/0.98      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.89/0.98      | ~ v1_funct_1(X0_50)
% 2.89/0.98      | ~ v1_funct_1(X1_50) ),
% 2.89/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_1240,plain,
% 2.89/0.98      ( r2_funct_2(u1_struct_0(X0_49),u1_struct_0(sK2),X0_50,X0_50)
% 2.89/0.98      | ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK2))
% 2.89/0.98      | ~ v1_funct_2(k2_tmap_1(sK1,sK2,sK5,X0_49),u1_struct_0(X0_49),u1_struct_0(sK2))
% 2.89/0.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK2))))
% 2.89/0.98      | ~ m1_subset_1(k2_tmap_1(sK1,sK2,sK5,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK2))))
% 2.89/0.98      | ~ v1_funct_1(X0_50)
% 2.89/0.98      | ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK5,X0_49)) ),
% 2.89/0.98      inference(instantiation,[status(thm)],[c_316]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_2653,plain,
% 2.89/0.98      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK4),k2_tmap_1(sK1,sK2,sK5,sK4))
% 2.89/0.98      | ~ v1_funct_2(k2_tmap_1(sK1,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
% 2.89/0.98      | ~ m1_subset_1(k2_tmap_1(sK1,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 2.89/0.98      | ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK5,sK4)) ),
% 2.89/0.98      inference(instantiation,[status(thm)],[c_1240]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_9,plain,
% 2.89/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.89/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.89/0.98      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 2.89/0.98      | ~ l1_struct_0(X3)
% 2.89/0.98      | ~ l1_struct_0(X2)
% 2.89/0.98      | ~ l1_struct_0(X1)
% 2.89/0.98      | ~ v1_funct_1(X0) ),
% 2.89/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_312,plain,
% 2.89/0.98      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 2.89/0.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 2.89/0.98      | m1_subset_1(k2_tmap_1(X0_49,X1_49,X0_50,X2_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_49),u1_struct_0(X1_49))))
% 2.89/0.98      | ~ l1_struct_0(X2_49)
% 2.89/0.98      | ~ l1_struct_0(X1_49)
% 2.89/0.98      | ~ l1_struct_0(X0_49)
% 2.89/0.98      | ~ v1_funct_1(X0_50) ),
% 2.89/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_1139,plain,
% 2.89/0.98      ( ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
% 2.89/0.98      | m1_subset_1(k2_tmap_1(sK1,sK2,sK5,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK2))))
% 2.89/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 2.89/0.98      | ~ l1_struct_0(X0_49)
% 2.89/0.98      | ~ l1_struct_0(sK1)
% 2.89/0.98      | ~ l1_struct_0(sK2)
% 2.89/0.98      | ~ v1_funct_1(sK5) ),
% 2.89/0.98      inference(instantiation,[status(thm)],[c_312]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_2020,plain,
% 2.89/0.98      ( ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
% 2.89/0.98      | m1_subset_1(k2_tmap_1(sK1,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 2.89/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 2.89/0.98      | ~ l1_struct_0(sK4)
% 2.89/0.98      | ~ l1_struct_0(sK1)
% 2.89/0.98      | ~ l1_struct_0(sK2)
% 2.89/0.98      | ~ v1_funct_1(sK5) ),
% 2.89/0.98      inference(instantiation,[status(thm)],[c_1139]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_11,plain,
% 2.89/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.89/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.89/0.98      | ~ l1_struct_0(X3)
% 2.89/0.98      | ~ l1_struct_0(X2)
% 2.89/0.98      | ~ l1_struct_0(X1)
% 2.89/0.98      | ~ v1_funct_1(X0)
% 2.89/0.98      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 2.89/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_310,plain,
% 2.89/0.98      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 2.89/0.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 2.89/0.98      | ~ l1_struct_0(X2_49)
% 2.89/0.98      | ~ l1_struct_0(X1_49)
% 2.89/0.98      | ~ l1_struct_0(X0_49)
% 2.89/0.98      | ~ v1_funct_1(X0_50)
% 2.89/0.98      | v1_funct_1(k2_tmap_1(X0_49,X1_49,X0_50,X2_49)) ),
% 2.89/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_1117,plain,
% 2.89/0.98      ( ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
% 2.89/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 2.89/0.98      | ~ l1_struct_0(X0_49)
% 2.89/0.98      | ~ l1_struct_0(sK1)
% 2.89/0.98      | ~ l1_struct_0(sK2)
% 2.89/0.98      | v1_funct_1(k2_tmap_1(sK1,sK2,sK5,X0_49))
% 2.89/0.98      | ~ v1_funct_1(sK5) ),
% 2.89/0.98      inference(instantiation,[status(thm)],[c_310]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_1917,plain,
% 2.89/0.98      ( ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
% 2.89/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 2.89/0.98      | ~ l1_struct_0(sK4)
% 2.89/0.98      | ~ l1_struct_0(sK1)
% 2.89/0.98      | ~ l1_struct_0(sK2)
% 2.89/0.98      | v1_funct_1(k2_tmap_1(sK1,sK2,sK5,sK4))
% 2.89/0.98      | ~ v1_funct_1(sK5) ),
% 2.89/0.98      inference(instantiation,[status(thm)],[c_1117]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_6,plain,
% 2.89/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.89/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_315,plain,
% 2.89/0.98      ( ~ l1_pre_topc(X0_49) | l1_struct_0(X0_49) ),
% 2.89/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_1840,plain,
% 2.89/0.98      ( ~ l1_pre_topc(sK4) | l1_struct_0(sK4) ),
% 2.89/0.98      inference(instantiation,[status(thm)],[c_315]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_18,negated_conjecture,
% 2.89/0.98      ( m1_pre_topc(sK4,sK1) ),
% 2.89/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_303,negated_conjecture,
% 2.89/0.98      ( m1_pre_topc(sK4,sK1) ),
% 2.89/0.98      inference(subtyping,[status(esa)],[c_18]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_825,plain,
% 2.89/0.98      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.89/0.98      inference(predicate_to_equality,[status(thm)],[c_303]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_7,plain,
% 2.89/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.89/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_314,plain,
% 2.89/0.98      ( ~ m1_pre_topc(X0_49,X1_49)
% 2.89/0.98      | ~ l1_pre_topc(X1_49)
% 2.89/0.98      | l1_pre_topc(X0_49) ),
% 2.89/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_814,plain,
% 2.89/0.98      ( m1_pre_topc(X0_49,X1_49) != iProver_top
% 2.89/0.98      | l1_pre_topc(X1_49) != iProver_top
% 2.89/0.98      | l1_pre_topc(X0_49) = iProver_top ),
% 2.89/0.98      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_1706,plain,
% 2.89/0.98      ( l1_pre_topc(sK4) = iProver_top
% 2.89/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.89/0.98      inference(superposition,[status(thm)],[c_825,c_814]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_1721,plain,
% 2.89/0.98      ( l1_pre_topc(sK4) | ~ l1_pre_topc(sK1) ),
% 2.89/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1706]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_10,plain,
% 2.89/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.89/0.98      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 2.89/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.89/0.98      | ~ l1_struct_0(X3)
% 2.89/0.98      | ~ l1_struct_0(X2)
% 2.89/0.98      | ~ l1_struct_0(X1)
% 2.89/0.98      | ~ v1_funct_1(X0) ),
% 2.89/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_311,plain,
% 2.89/0.98      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 2.89/0.98      | v1_funct_2(k2_tmap_1(X0_49,X1_49,X0_50,X2_49),u1_struct_0(X2_49),u1_struct_0(X1_49))
% 2.89/0.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 2.89/0.98      | ~ l1_struct_0(X2_49)
% 2.89/0.98      | ~ l1_struct_0(X1_49)
% 2.89/0.98      | ~ l1_struct_0(X0_49)
% 2.89/0.98      | ~ v1_funct_1(X0_50) ),
% 2.89/0.98      inference(subtyping,[status(esa)],[c_10]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_1132,plain,
% 2.89/0.98      ( v1_funct_2(k2_tmap_1(sK1,sK2,sK5,X0_49),u1_struct_0(X0_49),u1_struct_0(sK2))
% 2.89/0.98      | ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
% 2.89/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 2.89/0.98      | ~ l1_struct_0(X0_49)
% 2.89/0.98      | ~ l1_struct_0(sK1)
% 2.89/0.98      | ~ l1_struct_0(sK2)
% 2.89/0.98      | ~ v1_funct_1(sK5) ),
% 2.89/0.98      inference(instantiation,[status(thm)],[c_311]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_1498,plain,
% 2.89/0.98      ( v1_funct_2(k2_tmap_1(sK1,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
% 2.89/0.98      | ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
% 2.89/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 2.89/0.98      | ~ l1_struct_0(sK4)
% 2.89/0.98      | ~ l1_struct_0(sK1)
% 2.89/0.98      | ~ l1_struct_0(sK2)
% 2.89/0.98      | ~ v1_funct_1(sK5) ),
% 2.89/0.98      inference(instantiation,[status(thm)],[c_1132]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_12,plain,
% 2.89/0.98      ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_tmap_1(X3,X1,X4,X0))
% 2.89/0.98      | r2_funct_2(u1_struct_0(X5),u1_struct_0(X1),k3_tmap_1(X3,X1,X0,X5,X2),k2_tmap_1(X3,X1,X4,X5))
% 2.89/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.89/0.98      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
% 2.89/0.98      | ~ m1_pre_topc(X5,X3)
% 2.89/0.98      | ~ m1_pre_topc(X5,X0)
% 2.89/0.98      | ~ m1_pre_topc(X0,X3)
% 2.89/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.89/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.89/0.98      | v2_struct_0(X3)
% 2.89/0.98      | v2_struct_0(X1)
% 2.89/0.98      | v2_struct_0(X0)
% 2.89/0.98      | v2_struct_0(X5)
% 2.89/0.98      | ~ v2_pre_topc(X1)
% 2.89/0.98      | ~ v2_pre_topc(X3)
% 2.89/0.98      | ~ l1_pre_topc(X3)
% 2.89/0.98      | ~ l1_pre_topc(X1)
% 2.89/0.98      | ~ v1_funct_1(X2)
% 2.89/0.98      | ~ v1_funct_1(X4) ),
% 2.89/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_309,plain,
% 2.89/0.98      ( ~ r2_funct_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50,k2_tmap_1(X2_49,X1_49,X1_50,X0_49))
% 2.89/0.98      | r2_funct_2(u1_struct_0(X3_49),u1_struct_0(X1_49),k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50),k2_tmap_1(X2_49,X1_49,X1_50,X3_49))
% 2.89/0.98      | ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 2.89/0.98      | ~ v1_funct_2(X1_50,u1_struct_0(X2_49),u1_struct_0(X1_49))
% 2.89/0.98      | ~ m1_pre_topc(X3_49,X2_49)
% 2.89/0.98      | ~ m1_pre_topc(X3_49,X0_49)
% 2.89/0.98      | ~ m1_pre_topc(X0_49,X2_49)
% 2.89/0.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 2.89/0.98      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_49),u1_struct_0(X1_49))))
% 2.89/0.98      | v2_struct_0(X3_49)
% 2.89/0.98      | v2_struct_0(X1_49)
% 2.89/0.98      | v2_struct_0(X0_49)
% 2.89/0.98      | v2_struct_0(X2_49)
% 2.89/0.98      | ~ v2_pre_topc(X1_49)
% 2.89/0.98      | ~ v2_pre_topc(X2_49)
% 2.89/0.98      | ~ l1_pre_topc(X1_49)
% 2.89/0.98      | ~ l1_pre_topc(X2_49)
% 2.89/0.98      | ~ v1_funct_1(X0_50)
% 2.89/0.98      | ~ v1_funct_1(X1_50) ),
% 2.89/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_1179,plain,
% 2.89/0.98      ( ~ r2_funct_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50,k2_tmap_1(sK1,X1_49,X1_50,X0_49))
% 2.89/0.98      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1_49),k3_tmap_1(sK1,X1_49,X0_49,sK3,X0_50),k2_tmap_1(sK1,X1_49,X1_50,sK3))
% 2.89/0.98      | ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 2.89/0.98      | ~ v1_funct_2(X1_50,u1_struct_0(sK1),u1_struct_0(X1_49))
% 2.89/0.98      | ~ m1_pre_topc(X0_49,sK1)
% 2.89/0.98      | ~ m1_pre_topc(sK3,X0_49)
% 2.89/0.98      | ~ m1_pre_topc(sK3,sK1)
% 2.89/0.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 2.89/0.98      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1_49))))
% 2.89/0.98      | v2_struct_0(X1_49)
% 2.89/0.98      | v2_struct_0(X0_49)
% 2.89/0.98      | v2_struct_0(sK1)
% 2.89/0.98      | v2_struct_0(sK3)
% 2.89/0.98      | ~ v2_pre_topc(X1_49)
% 2.89/0.98      | ~ v2_pre_topc(sK1)
% 2.89/0.98      | ~ l1_pre_topc(X1_49)
% 2.89/0.98      | ~ l1_pre_topc(sK1)
% 2.89/0.98      | ~ v1_funct_1(X0_50)
% 2.89/0.98      | ~ v1_funct_1(X1_50) ),
% 2.89/0.98      inference(instantiation,[status(thm)],[c_309]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_1318,plain,
% 2.89/0.98      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_49),X0_50,k2_tmap_1(sK1,X0_49,X1_50,sK4))
% 2.89/0.98      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0_49),k3_tmap_1(sK1,X0_49,sK4,sK3,X0_50),k2_tmap_1(sK1,X0_49,X1_50,sK3))
% 2.89/0.98      | ~ v1_funct_2(X0_50,u1_struct_0(sK4),u1_struct_0(X0_49))
% 2.89/0.98      | ~ v1_funct_2(X1_50,u1_struct_0(sK1),u1_struct_0(X0_49))
% 2.89/0.98      | ~ m1_pre_topc(sK4,sK1)
% 2.89/0.98      | ~ m1_pre_topc(sK3,sK4)
% 2.89/0.98      | ~ m1_pre_topc(sK3,sK1)
% 2.89/0.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_49))))
% 2.89/0.98      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_49))))
% 2.89/0.98      | v2_struct_0(X0_49)
% 2.89/0.98      | v2_struct_0(sK4)
% 2.89/0.98      | v2_struct_0(sK1)
% 2.89/0.98      | v2_struct_0(sK3)
% 2.89/0.98      | ~ v2_pre_topc(X0_49)
% 2.89/0.98      | ~ v2_pre_topc(sK1)
% 2.89/0.98      | ~ l1_pre_topc(X0_49)
% 2.89/0.98      | ~ l1_pre_topc(sK1)
% 2.89/0.98      | ~ v1_funct_1(X0_50)
% 2.89/0.98      | ~ v1_funct_1(X1_50) ),
% 2.89/0.98      inference(instantiation,[status(thm)],[c_1179]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_1497,plain,
% 2.89/0.98      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK4),k2_tmap_1(sK1,sK2,X0_50,sK4))
% 2.89/0.98      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,k2_tmap_1(sK1,sK2,sK5,sK4)),k2_tmap_1(sK1,sK2,X0_50,sK3))
% 2.89/0.98      | ~ v1_funct_2(X0_50,u1_struct_0(sK1),u1_struct_0(sK2))
% 2.89/0.98      | ~ v1_funct_2(k2_tmap_1(sK1,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
% 2.89/0.98      | ~ m1_pre_topc(sK4,sK1)
% 2.89/0.98      | ~ m1_pre_topc(sK3,sK4)
% 2.89/0.98      | ~ m1_pre_topc(sK3,sK1)
% 2.89/0.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 2.89/0.98      | ~ m1_subset_1(k2_tmap_1(sK1,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 2.89/0.99      | v2_struct_0(sK4)
% 2.89/0.99      | v2_struct_0(sK1)
% 2.89/0.99      | v2_struct_0(sK2)
% 2.89/0.99      | v2_struct_0(sK3)
% 2.89/0.99      | ~ v2_pre_topc(sK1)
% 2.89/0.99      | ~ v2_pre_topc(sK2)
% 2.89/0.99      | ~ l1_pre_topc(sK1)
% 2.89/0.99      | ~ l1_pre_topc(sK2)
% 2.89/0.99      | ~ v1_funct_1(X0_50)
% 2.89/0.99      | ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK5,sK4)) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_1318]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1500,plain,
% 2.89/0.99      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK4),k2_tmap_1(sK1,sK2,sK5,sK4))
% 2.89/0.99      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,k2_tmap_1(sK1,sK2,sK5,sK4)),k2_tmap_1(sK1,sK2,sK5,sK3))
% 2.89/0.99      | ~ v1_funct_2(k2_tmap_1(sK1,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
% 2.89/0.99      | ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
% 2.89/0.99      | ~ m1_pre_topc(sK4,sK1)
% 2.89/0.99      | ~ m1_pre_topc(sK3,sK4)
% 2.89/0.99      | ~ m1_pre_topc(sK3,sK1)
% 2.89/0.99      | ~ m1_subset_1(k2_tmap_1(sK1,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 2.89/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 2.89/0.99      | v2_struct_0(sK4)
% 2.89/0.99      | v2_struct_0(sK1)
% 2.89/0.99      | v2_struct_0(sK2)
% 2.89/0.99      | v2_struct_0(sK3)
% 2.89/0.99      | ~ v2_pre_topc(sK1)
% 2.89/0.99      | ~ v2_pre_topc(sK2)
% 2.89/0.99      | ~ l1_pre_topc(sK1)
% 2.89/0.99      | ~ l1_pre_topc(sK2)
% 2.89/0.99      | ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK5,sK4))
% 2.89/0.99      | ~ v1_funct_1(sK5) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_1497]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1291,plain,
% 2.89/0.99      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_315]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_60,plain,
% 2.89/0.99      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_13,negated_conjecture,
% 2.89/0.99      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,k2_tmap_1(sK1,sK2,sK5,sK4)),k2_tmap_1(sK1,sK2,sK5,sK3)) ),
% 2.89/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_14,negated_conjecture,
% 2.89/0.99      ( m1_pre_topc(sK3,sK4) ),
% 2.89/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_15,negated_conjecture,
% 2.89/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 2.89/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_16,negated_conjecture,
% 2.89/0.99      ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.89/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_17,negated_conjecture,
% 2.89/0.99      ( v1_funct_1(sK5) ),
% 2.89/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_19,negated_conjecture,
% 2.89/0.99      ( ~ v2_struct_0(sK4) ),
% 2.89/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_20,negated_conjecture,
% 2.89/0.99      ( m1_pre_topc(sK3,sK1) ),
% 2.89/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_21,negated_conjecture,
% 2.89/0.99      ( ~ v2_struct_0(sK3) ),
% 2.89/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_22,negated_conjecture,
% 2.89/0.99      ( l1_pre_topc(sK2) ),
% 2.89/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_23,negated_conjecture,
% 2.89/0.99      ( v2_pre_topc(sK2) ),
% 2.89/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_24,negated_conjecture,
% 2.89/0.99      ( ~ v2_struct_0(sK2) ),
% 2.89/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_25,negated_conjecture,
% 2.89/0.99      ( l1_pre_topc(sK1) ),
% 2.89/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_26,negated_conjecture,
% 2.89/0.99      ( v2_pre_topc(sK1) ),
% 2.89/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_27,negated_conjecture,
% 2.89/0.99      ( ~ v2_struct_0(sK1) ),
% 2.89/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(contradiction,plain,
% 2.89/0.99      ( $false ),
% 2.89/0.99      inference(minisat,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_2653,c_2020,c_1917,c_1840,c_1721,c_1498,c_1500,c_1291,
% 2.89/0.99                 c_60,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,
% 2.89/0.99                 c_23,c_24,c_25,c_26,c_27]) ).
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.89/0.99  
% 2.89/0.99  ------                               Statistics
% 2.89/0.99  
% 2.89/0.99  ------ General
% 2.89/0.99  
% 2.89/0.99  abstr_ref_over_cycles:                  0
% 2.89/0.99  abstr_ref_under_cycles:                 0
% 2.89/0.99  gc_basic_clause_elim:                   0
% 2.89/0.99  forced_gc_time:                         0
% 2.89/0.99  parsing_time:                           0.01
% 2.89/0.99  unif_index_cands_time:                  0.
% 2.89/0.99  unif_index_add_time:                    0.
% 2.89/0.99  orderings_time:                         0.
% 2.89/0.99  out_proof_time:                         0.008
% 2.89/0.99  total_time:                             0.131
% 2.89/0.99  num_of_symbols:                         54
% 2.89/0.99  num_of_terms:                           2843
% 2.89/0.99  
% 2.89/0.99  ------ Preprocessing
% 2.89/0.99  
% 2.89/0.99  num_of_splits:                          0
% 2.89/0.99  num_of_split_atoms:                     0
% 2.89/0.99  num_of_reused_defs:                     0
% 2.89/0.99  num_eq_ax_congr_red:                    32
% 2.89/0.99  num_of_sem_filtered_clauses:            1
% 2.89/0.99  num_of_subtypes:                        5
% 2.89/0.99  monotx_restored_types:                  0
% 2.89/0.99  sat_num_of_epr_types:                   0
% 2.89/0.99  sat_num_of_non_cyclic_types:            0
% 2.89/0.99  sat_guarded_non_collapsed_types:        0
% 2.89/0.99  num_pure_diseq_elim:                    0
% 2.89/0.99  simp_replaced_by:                       0
% 2.89/0.99  res_preprocessed:                       101
% 2.89/0.99  prep_upred:                             0
% 2.89/0.99  prep_unflattend:                        0
% 2.89/0.99  smt_new_axioms:                         0
% 2.89/0.99  pred_elim_cands:                        9
% 2.89/0.99  pred_elim:                              0
% 2.89/0.99  pred_elim_cl:                           0
% 2.89/0.99  pred_elim_cycles:                       1
% 2.89/0.99  merged_defs:                            0
% 2.89/0.99  merged_defs_ncl:                        0
% 2.89/0.99  bin_hyper_res:                          0
% 2.89/0.99  prep_cycles:                            3
% 2.89/0.99  pred_elim_time:                         0.
% 2.89/0.99  splitting_time:                         0.
% 2.89/0.99  sem_filter_time:                        0.
% 2.89/0.99  monotx_time:                            0.
% 2.89/0.99  subtype_inf_time:                       0.
% 2.89/0.99  
% 2.89/0.99  ------ Problem properties
% 2.89/0.99  
% 2.89/0.99  clauses:                                28
% 2.89/0.99  conjectures:                            15
% 2.89/0.99  epr:                                    14
% 2.89/0.99  horn:                                   26
% 2.89/0.99  ground:                                 15
% 2.89/0.99  unary:                                  18
% 2.89/0.99  binary:                                 1
% 2.89/0.99  lits:                                   87
% 2.89/0.99  lits_eq:                                1
% 2.89/0.99  fd_pure:                                0
% 2.89/0.99  fd_pseudo:                              0
% 2.89/0.99  fd_cond:                                0
% 2.89/0.99  fd_pseudo_cond:                         0
% 2.89/0.99  ac_symbols:                             0
% 2.89/0.99  
% 2.89/0.99  ------ Propositional Solver
% 2.89/0.99  
% 2.89/0.99  prop_solver_calls:                      23
% 2.89/0.99  prop_fast_solver_calls:                 726
% 2.89/0.99  smt_solver_calls:                       0
% 2.89/0.99  smt_fast_solver_calls:                  0
% 2.89/0.99  prop_num_of_clauses:                    774
% 2.89/0.99  prop_preprocess_simplified:             3267
% 2.89/0.99  prop_fo_subsumed:                       13
% 2.89/0.99  prop_solver_time:                       0.
% 2.89/0.99  smt_solver_time:                        0.
% 2.89/0.99  smt_fast_solver_time:                   0.
% 2.89/0.99  prop_fast_solver_time:                  0.
% 2.89/0.99  prop_unsat_core_time:                   0.
% 2.89/0.99  
% 2.89/0.99  ------ QBF
% 2.89/0.99  
% 2.89/0.99  qbf_q_res:                              0
% 2.89/0.99  qbf_num_tautologies:                    0
% 2.89/0.99  qbf_prep_cycles:                        0
% 2.89/0.99  
% 2.89/0.99  ------ BMC1
% 2.89/0.99  
% 2.89/0.99  bmc1_current_bound:                     -1
% 2.89/0.99  bmc1_last_solved_bound:                 -1
% 2.89/0.99  bmc1_unsat_core_size:                   -1
% 2.89/0.99  bmc1_unsat_core_parents_size:           -1
% 2.89/0.99  bmc1_merge_next_fun:                    0
% 2.89/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.89/0.99  
% 2.89/0.99  ------ Instantiation
% 2.89/0.99  
% 2.89/0.99  inst_num_of_clauses:                    220
% 2.89/0.99  inst_num_in_passive:                    58
% 2.89/0.99  inst_num_in_active:                     156
% 2.89/0.99  inst_num_in_unprocessed:                5
% 2.89/0.99  inst_num_of_loops:                      186
% 2.89/0.99  inst_num_of_learning_restarts:          0
% 2.89/0.99  inst_num_moves_active_passive:          25
% 2.89/0.99  inst_lit_activity:                      0
% 2.89/0.99  inst_lit_activity_moves:                0
% 2.89/0.99  inst_num_tautologies:                   0
% 2.89/0.99  inst_num_prop_implied:                  0
% 2.89/0.99  inst_num_existing_simplified:           0
% 2.89/0.99  inst_num_eq_res_simplified:             0
% 2.89/0.99  inst_num_child_elim:                    0
% 2.89/0.99  inst_num_of_dismatching_blockings:      144
% 2.89/0.99  inst_num_of_non_proper_insts:           275
% 2.89/0.99  inst_num_of_duplicates:                 0
% 2.89/0.99  inst_inst_num_from_inst_to_res:         0
% 2.89/0.99  inst_dismatching_checking_time:         0.
% 2.89/0.99  
% 2.89/0.99  ------ Resolution
% 2.89/0.99  
% 2.89/0.99  res_num_of_clauses:                     0
% 2.89/0.99  res_num_in_passive:                     0
% 2.89/0.99  res_num_in_active:                      0
% 2.89/0.99  res_num_of_loops:                       104
% 2.89/0.99  res_forward_subset_subsumed:            8
% 2.89/0.99  res_backward_subset_subsumed:           2
% 2.89/0.99  res_forward_subsumed:                   0
% 2.89/0.99  res_backward_subsumed:                  0
% 2.89/0.99  res_forward_subsumption_resolution:     0
% 2.89/0.99  res_backward_subsumption_resolution:    0
% 2.89/0.99  res_clause_to_clause_subsumption:       109
% 2.89/0.99  res_orphan_elimination:                 0
% 2.89/0.99  res_tautology_del:                      9
% 2.89/0.99  res_num_eq_res_simplified:              0
% 2.89/0.99  res_num_sel_changes:                    0
% 2.89/0.99  res_moves_from_active_to_pass:          0
% 2.89/0.99  
% 2.89/0.99  ------ Superposition
% 2.89/0.99  
% 2.89/0.99  sup_time_total:                         0.
% 2.89/0.99  sup_time_generating:                    0.
% 2.89/0.99  sup_time_sim_full:                      0.
% 2.89/0.99  sup_time_sim_immed:                     0.
% 2.89/0.99  
% 2.89/0.99  sup_num_of_clauses:                     50
% 2.89/0.99  sup_num_in_active:                      36
% 2.89/0.99  sup_num_in_passive:                     14
% 2.89/0.99  sup_num_of_loops:                       36
% 2.89/0.99  sup_fw_superposition:                   17
% 2.89/0.99  sup_bw_superposition:                   6
% 2.89/0.99  sup_immediate_simplified:               1
% 2.89/0.99  sup_given_eliminated:                   0
% 2.89/0.99  comparisons_done:                       0
% 2.89/0.99  comparisons_avoided:                    0
% 2.89/0.99  
% 2.89/0.99  ------ Simplifications
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  sim_fw_subset_subsumed:                 0
% 2.89/0.99  sim_bw_subset_subsumed:                 0
% 2.89/0.99  sim_fw_subsumed:                        0
% 2.89/0.99  sim_bw_subsumed:                        0
% 2.89/0.99  sim_fw_subsumption_res:                 1
% 2.89/0.99  sim_bw_subsumption_res:                 0
% 2.89/0.99  sim_tautology_del:                      0
% 2.89/0.99  sim_eq_tautology_del:                   0
% 2.89/0.99  sim_eq_res_simp:                        0
% 2.89/0.99  sim_fw_demodulated:                     0
% 2.89/0.99  sim_bw_demodulated:                     0
% 2.89/0.99  sim_light_normalised:                   0
% 2.89/0.99  sim_joinable_taut:                      0
% 2.89/0.99  sim_joinable_simp:                      0
% 2.89/0.99  sim_ac_normalised:                      0
% 2.89/0.99  sim_smt_subsumption:                    0
% 2.89/0.99  
%------------------------------------------------------------------------------
