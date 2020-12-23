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
% DateTime   : Thu Dec  3 12:22:58 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :  170 (2594 expanded)
%              Number of clauses        :  114 ( 564 expanded)
%              Number of leaves         :   14 (1067 expanded)
%              Depth                    :   31
%              Number of atoms          : 1015 (32046 expanded)
%              Number of equality atoms :  307 ( 873 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal clause size      :   30 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
          & m1_pre_topc(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,sK4,X3)),k2_tmap_1(X0,X1,sK4,X2))
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,k2_tmap_1(X0,X1,X4,sK3)),k2_tmap_1(X0,X1,X4,X2))
            & m1_pre_topc(X2,sK3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
                ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,sK2))
                & m1_pre_topc(sK2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,k2_tmap_1(X0,sK1,X4,X3)),k2_tmap_1(X0,sK1,X4,X2))
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
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
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,k2_tmap_1(sK0,X1,X4,X3)),k2_tmap_1(sK0,X1,X4,X2))
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
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

fof(f31,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK4)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f25,f30,f29,f28,f27,f26])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f35,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f34,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f40,plain,(
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
    inference(cnf_transformation,[],[f21])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_274,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_736,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_274])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_280,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k2_tmap_1(X0_48,X1_48,X0_49,X2_48))
    | ~ l1_struct_0(X2_48)
    | ~ l1_struct_0(X1_48)
    | ~ l1_struct_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_730,plain,
    ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_48,X1_48,X0_49,X2_48)) = iProver_top
    | l1_struct_0(X2_48) != iProver_top
    | l1_struct_0(X1_48) != iProver_top
    | l1_struct_0(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_280])).

cnf(c_1547,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_48)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_struct_0(X0_48) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_730])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_27,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_35,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_36,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_65,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_67,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_struct_0(sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_267,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_743,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_267])).

cnf(c_286,plain,
    ( ~ l1_pre_topc(X0_48)
    | l1_struct_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_724,plain,
    ( l1_pre_topc(X0_48) != iProver_top
    | l1_struct_0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_286])).

cnf(c_1200,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_743,c_724])).

cnf(c_1833,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_48)) = iProver_top
    | l1_struct_0(X0_48) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1547,c_27,c_35,c_36,c_67,c_1200])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_281,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | v1_funct_2(k2_tmap_1(X0_48,X1_48,X0_49,X2_48),u1_struct_0(X2_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ v1_funct_1(X0_49)
    | ~ l1_struct_0(X2_48)
    | ~ l1_struct_0(X1_48)
    | ~ l1_struct_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_729,plain,
    ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_48,X1_48,X0_49,X2_48),u1_struct_0(X2_48),u1_struct_0(X1_48)) = iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_struct_0(X2_48) != iProver_top
    | l1_struct_0(X1_48) != iProver_top
    | l1_struct_0(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_282,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | m1_subset_1(k2_tmap_1(X0_48,X1_48,X0_49,X2_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48))))
    | ~ v1_funct_1(X0_49)
    | ~ l1_struct_0(X2_48)
    | ~ l1_struct_0(X1_48)
    | ~ l1_struct_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_728,plain,
    ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_48,X1_48,X0_49,X2_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48)))) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_struct_0(X2_48) != iProver_top
    | l1_struct_0(X1_48) != iProver_top
    | l1_struct_0(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_271,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_739,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_271])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_283,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ m1_pre_topc(X0_48,X2_48)
    | ~ m1_pre_topc(X3_48,X2_48)
    | ~ m1_pre_topc(X3_48,X0_48)
    | v2_struct_0(X2_48)
    | v2_struct_0(X1_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X2_48)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X2_48)
    | ~ l1_pre_topc(X1_48)
    | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X3_48)) = k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_727,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49)
    | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | m1_pre_topc(X0_48,X3_48) != iProver_top
    | m1_pre_topc(X2_48,X3_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X3_48) = iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X3_48) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X3_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_2211,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK0,X0_48,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X0_48,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_727])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_28,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_29,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_30,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2443,plain,
    ( l1_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK0,X0_48,sK4)
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X0_48,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2211,c_28,c_29,c_30,c_35,c_36])).

cnf(c_2444,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK0,X0_48,sK4)
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X0_48,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_2443])).

cnf(c_2457,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_739,c_2444])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_284,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ m1_pre_topc(X2_48,X0_48)
    | v2_struct_0(X1_48)
    | v2_struct_0(X0_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X0_48)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X0_48)
    | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k2_tmap_1(X0_48,X1_48,X0_49,X2_48) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_726,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k2_tmap_1(X0_48,X1_48,X0_49,X2_48)
    | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X0_48) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_1509,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k2_tmap_1(sK0,sK1,sK4,X0_48)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_726])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_25,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_26,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2052,plain,
    ( m1_pre_topc(X0_48,sK0) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k2_tmap_1(sK0,sK1,sK4,X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1509,c_25,c_26,c_27,c_28,c_29,c_30,c_35,c_36])).

cnf(c_2053,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k2_tmap_1(sK0,sK1,sK4,X0_48)
    | m1_pre_topc(X0_48,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2052])).

cnf(c_2060,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_739,c_2053])).

cnf(c_2491,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2457,c_2060])).

cnf(c_34,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_46,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_48,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_2799,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2491,c_25,c_26,c_27,c_34,c_48])).

cnf(c_279,plain,
    ( m1_pre_topc(X0_48,X0_48)
    | ~ l1_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_731,plain,
    ( m1_pre_topc(X0_48,X0_48) = iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_279])).

cnf(c_2459,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k3_tmap_1(X0_48,sK1,sK0,X0_48,sK4)
    | m1_pre_topc(X0_48,sK0) != iProver_top
    | m1_pre_topc(sK0,X0_48) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_pre_topc(X0_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_731,c_2444])).

cnf(c_2524,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k3_tmap_1(sK0,sK1,sK0,sK0,sK4)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_731,c_2459])).

cnf(c_2062,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_731,c_2053])).

cnf(c_47,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1028,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X0_48,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k2_tmap_1(sK0,sK1,sK4,X0_48) ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_1030,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0) ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_2374,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2062,c_24,c_23,c_22,c_21,c_20,c_19,c_14,c_13,c_12,c_47,c_1030])).

cnf(c_2530,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK0,sK4) = k2_tmap_1(sK0,sK1,sK4,sK0)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2524,c_2374])).

cnf(c_2977,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK0,sK4) = k2_tmap_1(sK0,sK1,sK4,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2530,c_25,c_26,c_27,c_48])).

cnf(c_8,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_278,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,k3_tmap_1(X2_48,X1_48,X0_48,X0_48,X0_49))
    | ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ m1_pre_topc(X0_48,X2_48)
    | v2_struct_0(X1_48)
    | v2_struct_0(X0_48)
    | v2_struct_0(X2_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X2_48)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X2_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_732,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,k3_tmap_1(X2_48,X1_48,X0_48,X0_48,X0_49)) = iProver_top
    | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X0_48,X2_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_2980,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2977,c_732])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3118,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2980,c_25,c_26,c_27,c_28,c_29,c_30,c_35,c_36,c_37,c_48])).

cnf(c_9,plain,
    ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_tmap_1(X3,X1,X4,X0))
    | r2_funct_2(u1_struct_0(X5),u1_struct_0(X1),k3_tmap_1(X3,X1,X0,X5,X2),k2_tmap_1(X3,X1,X4,X5))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X5,X3)
    | ~ m1_pre_topc(X5,X0)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_277,plain,
    ( ~ r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,k2_tmap_1(X2_48,X1_48,X1_49,X0_48))
    | r2_funct_2(u1_struct_0(X3_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k2_tmap_1(X2_48,X1_48,X1_49,X3_48))
    | ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ v1_funct_2(X1_49,u1_struct_0(X2_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48))))
    | ~ m1_pre_topc(X3_48,X2_48)
    | ~ m1_pre_topc(X3_48,X0_48)
    | ~ m1_pre_topc(X0_48,X2_48)
    | v2_struct_0(X3_48)
    | v2_struct_0(X1_48)
    | v2_struct_0(X0_48)
    | v2_struct_0(X2_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X2_48)
    | ~ v1_funct_1(X1_49)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X2_48) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_733,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,k2_tmap_1(X2_48,X1_48,X1_49,X0_48)) != iProver_top
    | r2_funct_2(u1_struct_0(X3_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k2_tmap_1(X2_48,X1_48,X1_49,X3_48)) = iProver_top
    | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | v1_funct_2(X1_49,u1_struct_0(X2_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X3_48,X0_48) != iProver_top
    | m1_pre_topc(X0_48,X2_48) != iProver_top
    | m1_pre_topc(X3_48,X2_48) != iProver_top
    | v2_struct_0(X3_48) = iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(X1_49) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_277])).

cnf(c_3123,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_48,sK4),k2_tmap_1(sK0,sK1,sK4,X0_48)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_48,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3118,c_733])).

cnf(c_3128,plain,
    ( v2_struct_0(X0_48) = iProver_top
    | r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_48,sK4),k2_tmap_1(sK0,sK1,sK4,X0_48)) = iProver_top
    | m1_pre_topc(X0_48,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3123,c_25,c_26,c_27,c_28,c_29,c_30,c_35,c_36,c_37,c_48])).

cnf(c_3129,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_48,sK4),k2_tmap_1(sK0,sK1,sK4,X0_48)) = iProver_top
    | m1_pre_topc(X0_48,sK0) != iProver_top
    | v2_struct_0(X0_48) = iProver_top ),
    inference(renaming,[status(thm)],[c_3128])).

cnf(c_3138,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2799,c_3129])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_33,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4598,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3138,c_33,c_34])).

cnf(c_4603,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,X0_48,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,X0_48)) = iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | m1_pre_topc(X0_48,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4598,c_733])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_31,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_32,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_38,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_39,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1143,plain,
    ( ~ r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49,k2_tmap_1(X1_48,sK1,X1_49,X0_48))
    | r2_funct_2(u1_struct_0(X2_48),u1_struct_0(sK1),k3_tmap_1(X1_48,sK1,X0_48,X2_48,X0_49),k2_tmap_1(X1_48,sK1,X1_49,X2_48))
    | ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(sK1))
    | ~ v1_funct_2(X1_49,u1_struct_0(X1_48),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(sK1))))
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_48),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X2_48,X0_48)
    | ~ m1_pre_topc(X0_48,X1_48)
    | ~ m1_pre_topc(X2_48,X1_48)
    | v2_struct_0(X1_48)
    | v2_struct_0(X0_48)
    | v2_struct_0(X2_48)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(X1_49)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_277])).

cnf(c_6103,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1143])).

cnf(c_6104,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6103])).

cnf(c_8365,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4603,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_3138,c_6104])).

cnf(c_8366,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8365])).

cnf(c_8372,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_728,c_8366])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_285,plain,
    ( ~ m1_pre_topc(X0_48,X1_48)
    | ~ l1_pre_topc(X1_48)
    | l1_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_725,plain,
    ( m1_pre_topc(X0_48,X1_48) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_285])).

cnf(c_1358,plain,
    ( l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_739,c_725])).

cnf(c_1820,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1358,c_27])).

cnf(c_1825,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1820,c_724])).

cnf(c_8736,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8372,c_27,c_35,c_36,c_37,c_67,c_1200,c_1825])).

cnf(c_8742,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_729,c_8736])).

cnf(c_8745,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8742,c_27,c_35,c_36,c_37,c_67,c_1200,c_1825])).

cnf(c_8750,plain,
    ( l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1833,c_8745])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8750,c_1825])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.10  % Command    : iproveropt_run.sh %d %s
% 0.10/0.30  % Computer   : n016.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 17:33:19 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  % Running in FOF mode
% 3.36/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/0.97  
% 3.36/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.36/0.97  
% 3.36/0.97  ------  iProver source info
% 3.36/0.97  
% 3.36/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.36/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.36/0.97  git: non_committed_changes: false
% 3.36/0.97  git: last_make_outside_of_git: false
% 3.36/0.97  
% 3.36/0.97  ------ 
% 3.36/0.97  
% 3.36/0.97  ------ Input Options
% 3.36/0.97  
% 3.36/0.97  --out_options                           all
% 3.36/0.97  --tptp_safe_out                         true
% 3.36/0.97  --problem_path                          ""
% 3.36/0.97  --include_path                          ""
% 3.36/0.97  --clausifier                            res/vclausify_rel
% 3.36/0.97  --clausifier_options                    --mode clausify
% 3.36/0.97  --stdin                                 false
% 3.36/0.97  --stats_out                             all
% 3.36/0.97  
% 3.36/0.97  ------ General Options
% 3.36/0.97  
% 3.36/0.97  --fof                                   false
% 3.36/0.97  --time_out_real                         305.
% 3.36/0.97  --time_out_virtual                      -1.
% 3.36/0.97  --symbol_type_check                     false
% 3.36/0.97  --clausify_out                          false
% 3.36/0.97  --sig_cnt_out                           false
% 3.36/0.97  --trig_cnt_out                          false
% 3.36/0.97  --trig_cnt_out_tolerance                1.
% 3.36/0.97  --trig_cnt_out_sk_spl                   false
% 3.36/0.97  --abstr_cl_out                          false
% 3.36/0.97  
% 3.36/0.97  ------ Global Options
% 3.36/0.97  
% 3.36/0.97  --schedule                              default
% 3.36/0.97  --add_important_lit                     false
% 3.36/0.97  --prop_solver_per_cl                    1000
% 3.36/0.97  --min_unsat_core                        false
% 3.36/0.97  --soft_assumptions                      false
% 3.36/0.97  --soft_lemma_size                       3
% 3.36/0.97  --prop_impl_unit_size                   0
% 3.36/0.97  --prop_impl_unit                        []
% 3.36/0.97  --share_sel_clauses                     true
% 3.36/0.97  --reset_solvers                         false
% 3.36/0.97  --bc_imp_inh                            [conj_cone]
% 3.36/0.97  --conj_cone_tolerance                   3.
% 3.36/0.97  --extra_neg_conj                        none
% 3.36/0.97  --large_theory_mode                     true
% 3.36/0.97  --prolific_symb_bound                   200
% 3.36/0.97  --lt_threshold                          2000
% 3.36/0.97  --clause_weak_htbl                      true
% 3.36/0.97  --gc_record_bc_elim                     false
% 3.36/0.97  
% 3.36/0.97  ------ Preprocessing Options
% 3.36/0.97  
% 3.36/0.97  --preprocessing_flag                    true
% 3.36/0.97  --time_out_prep_mult                    0.1
% 3.36/0.97  --splitting_mode                        input
% 3.36/0.97  --splitting_grd                         true
% 3.36/0.97  --splitting_cvd                         false
% 3.36/0.97  --splitting_cvd_svl                     false
% 3.36/0.97  --splitting_nvd                         32
% 3.36/0.97  --sub_typing                            true
% 3.36/0.97  --prep_gs_sim                           true
% 3.36/0.97  --prep_unflatten                        true
% 3.36/0.97  --prep_res_sim                          true
% 3.36/0.97  --prep_upred                            true
% 3.36/0.97  --prep_sem_filter                       exhaustive
% 3.36/0.97  --prep_sem_filter_out                   false
% 3.36/0.97  --pred_elim                             true
% 3.36/0.97  --res_sim_input                         true
% 3.36/0.97  --eq_ax_congr_red                       true
% 3.36/0.97  --pure_diseq_elim                       true
% 3.36/0.97  --brand_transform                       false
% 3.36/0.97  --non_eq_to_eq                          false
% 3.36/0.97  --prep_def_merge                        true
% 3.36/0.97  --prep_def_merge_prop_impl              false
% 3.36/0.97  --prep_def_merge_mbd                    true
% 3.36/0.97  --prep_def_merge_tr_red                 false
% 3.36/0.97  --prep_def_merge_tr_cl                  false
% 3.36/0.97  --smt_preprocessing                     true
% 3.36/0.97  --smt_ac_axioms                         fast
% 3.36/0.97  --preprocessed_out                      false
% 3.36/0.97  --preprocessed_stats                    false
% 3.36/0.97  
% 3.36/0.97  ------ Abstraction refinement Options
% 3.36/0.97  
% 3.36/0.97  --abstr_ref                             []
% 3.36/0.97  --abstr_ref_prep                        false
% 3.36/0.97  --abstr_ref_until_sat                   false
% 3.36/0.97  --abstr_ref_sig_restrict                funpre
% 3.36/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.36/0.97  --abstr_ref_under                       []
% 3.36/0.97  
% 3.36/0.97  ------ SAT Options
% 3.36/0.97  
% 3.36/0.97  --sat_mode                              false
% 3.36/0.97  --sat_fm_restart_options                ""
% 3.36/0.97  --sat_gr_def                            false
% 3.36/0.97  --sat_epr_types                         true
% 3.36/0.97  --sat_non_cyclic_types                  false
% 3.36/0.97  --sat_finite_models                     false
% 3.36/0.97  --sat_fm_lemmas                         false
% 3.36/0.97  --sat_fm_prep                           false
% 3.36/0.97  --sat_fm_uc_incr                        true
% 3.36/0.97  --sat_out_model                         small
% 3.36/0.97  --sat_out_clauses                       false
% 3.36/0.97  
% 3.36/0.97  ------ QBF Options
% 3.36/0.97  
% 3.36/0.97  --qbf_mode                              false
% 3.36/0.97  --qbf_elim_univ                         false
% 3.36/0.97  --qbf_dom_inst                          none
% 3.36/0.97  --qbf_dom_pre_inst                      false
% 3.36/0.97  --qbf_sk_in                             false
% 3.36/0.97  --qbf_pred_elim                         true
% 3.36/0.97  --qbf_split                             512
% 3.36/0.97  
% 3.36/0.97  ------ BMC1 Options
% 3.36/0.97  
% 3.36/0.97  --bmc1_incremental                      false
% 3.36/0.97  --bmc1_axioms                           reachable_all
% 3.36/0.97  --bmc1_min_bound                        0
% 3.36/0.97  --bmc1_max_bound                        -1
% 3.36/0.97  --bmc1_max_bound_default                -1
% 3.36/0.97  --bmc1_symbol_reachability              true
% 3.36/0.97  --bmc1_property_lemmas                  false
% 3.36/0.97  --bmc1_k_induction                      false
% 3.36/0.97  --bmc1_non_equiv_states                 false
% 3.36/0.97  --bmc1_deadlock                         false
% 3.36/0.97  --bmc1_ucm                              false
% 3.36/0.97  --bmc1_add_unsat_core                   none
% 3.36/0.97  --bmc1_unsat_core_children              false
% 3.36/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.36/0.97  --bmc1_out_stat                         full
% 3.36/0.97  --bmc1_ground_init                      false
% 3.36/0.97  --bmc1_pre_inst_next_state              false
% 3.36/0.97  --bmc1_pre_inst_state                   false
% 3.36/0.97  --bmc1_pre_inst_reach_state             false
% 3.36/0.97  --bmc1_out_unsat_core                   false
% 3.36/0.97  --bmc1_aig_witness_out                  false
% 3.36/0.97  --bmc1_verbose                          false
% 3.36/0.97  --bmc1_dump_clauses_tptp                false
% 3.36/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.36/0.97  --bmc1_dump_file                        -
% 3.36/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.36/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.36/0.97  --bmc1_ucm_extend_mode                  1
% 3.36/0.97  --bmc1_ucm_init_mode                    2
% 3.36/0.97  --bmc1_ucm_cone_mode                    none
% 3.36/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.36/0.97  --bmc1_ucm_relax_model                  4
% 3.36/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.36/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.36/0.97  --bmc1_ucm_layered_model                none
% 3.36/0.97  --bmc1_ucm_max_lemma_size               10
% 3.36/0.97  
% 3.36/0.97  ------ AIG Options
% 3.36/0.97  
% 3.36/0.97  --aig_mode                              false
% 3.36/0.97  
% 3.36/0.97  ------ Instantiation Options
% 3.36/0.97  
% 3.36/0.97  --instantiation_flag                    true
% 3.36/0.97  --inst_sos_flag                         false
% 3.36/0.97  --inst_sos_phase                        true
% 3.36/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.36/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.36/0.97  --inst_lit_sel_side                     num_symb
% 3.36/0.97  --inst_solver_per_active                1400
% 3.36/0.97  --inst_solver_calls_frac                1.
% 3.36/0.97  --inst_passive_queue_type               priority_queues
% 3.36/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.36/0.97  --inst_passive_queues_freq              [25;2]
% 3.36/0.97  --inst_dismatching                      true
% 3.36/0.97  --inst_eager_unprocessed_to_passive     true
% 3.36/0.97  --inst_prop_sim_given                   true
% 3.36/0.97  --inst_prop_sim_new                     false
% 3.36/0.97  --inst_subs_new                         false
% 3.36/0.97  --inst_eq_res_simp                      false
% 3.36/0.97  --inst_subs_given                       false
% 3.36/0.97  --inst_orphan_elimination               true
% 3.36/0.97  --inst_learning_loop_flag               true
% 3.36/0.97  --inst_learning_start                   3000
% 3.36/0.97  --inst_learning_factor                  2
% 3.36/0.97  --inst_start_prop_sim_after_learn       3
% 3.36/0.97  --inst_sel_renew                        solver
% 3.36/0.97  --inst_lit_activity_flag                true
% 3.36/0.97  --inst_restr_to_given                   false
% 3.36/0.97  --inst_activity_threshold               500
% 3.36/0.97  --inst_out_proof                        true
% 3.36/0.97  
% 3.36/0.97  ------ Resolution Options
% 3.36/0.97  
% 3.36/0.97  --resolution_flag                       true
% 3.36/0.97  --res_lit_sel                           adaptive
% 3.36/0.97  --res_lit_sel_side                      none
% 3.36/0.97  --res_ordering                          kbo
% 3.36/0.97  --res_to_prop_solver                    active
% 3.36/0.97  --res_prop_simpl_new                    false
% 3.36/0.97  --res_prop_simpl_given                  true
% 3.36/0.97  --res_passive_queue_type                priority_queues
% 3.36/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.36/0.97  --res_passive_queues_freq               [15;5]
% 3.36/0.97  --res_forward_subs                      full
% 3.36/0.97  --res_backward_subs                     full
% 3.36/0.97  --res_forward_subs_resolution           true
% 3.36/0.97  --res_backward_subs_resolution          true
% 3.36/0.97  --res_orphan_elimination                true
% 3.36/0.97  --res_time_limit                        2.
% 3.36/0.97  --res_out_proof                         true
% 3.36/0.97  
% 3.36/0.97  ------ Superposition Options
% 3.36/0.97  
% 3.36/0.97  --superposition_flag                    true
% 3.36/0.97  --sup_passive_queue_type                priority_queues
% 3.36/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.36/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.36/0.97  --demod_completeness_check              fast
% 3.36/0.97  --demod_use_ground                      true
% 3.36/0.97  --sup_to_prop_solver                    passive
% 3.36/0.97  --sup_prop_simpl_new                    true
% 3.36/0.97  --sup_prop_simpl_given                  true
% 3.36/0.97  --sup_fun_splitting                     false
% 3.36/0.97  --sup_smt_interval                      50000
% 3.36/0.97  
% 3.36/0.97  ------ Superposition Simplification Setup
% 3.36/0.97  
% 3.36/0.97  --sup_indices_passive                   []
% 3.36/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.36/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.97  --sup_full_bw                           [BwDemod]
% 3.36/0.97  --sup_immed_triv                        [TrivRules]
% 3.36/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.36/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.97  --sup_immed_bw_main                     []
% 3.36/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.36/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/0.97  
% 3.36/0.97  ------ Combination Options
% 3.36/0.97  
% 3.36/0.97  --comb_res_mult                         3
% 3.36/0.97  --comb_sup_mult                         2
% 3.36/0.97  --comb_inst_mult                        10
% 3.36/0.97  
% 3.36/0.97  ------ Debug Options
% 3.36/0.97  
% 3.36/0.97  --dbg_backtrace                         false
% 3.36/0.97  --dbg_dump_prop_clauses                 false
% 3.36/0.97  --dbg_dump_prop_clauses_file            -
% 3.36/0.97  --dbg_out_stat                          false
% 3.36/0.97  ------ Parsing...
% 3.36/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.36/0.97  
% 3.36/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.36/0.97  
% 3.36/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.36/0.97  
% 3.36/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.36/0.97  ------ Proving...
% 3.36/0.97  ------ Problem Properties 
% 3.36/0.97  
% 3.36/0.97  
% 3.36/0.97  clauses                                 25
% 3.36/0.97  conjectures                             15
% 3.36/0.97  EPR                                     15
% 3.36/0.97  Horn                                    21
% 3.36/0.97  unary                                   15
% 3.36/0.97  binary                                  2
% 3.36/0.97  lits                                    98
% 3.36/0.97  lits eq                                 2
% 3.36/0.97  fd_pure                                 0
% 3.36/0.97  fd_pseudo                               0
% 3.36/0.97  fd_cond                                 0
% 3.36/0.97  fd_pseudo_cond                          0
% 3.36/0.97  AC symbols                              0
% 3.36/0.97  
% 3.36/0.97  ------ Schedule dynamic 5 is on 
% 3.36/0.97  
% 3.36/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.36/0.97  
% 3.36/0.97  
% 3.36/0.97  ------ 
% 3.36/0.97  Current options:
% 3.36/0.97  ------ 
% 3.36/0.97  
% 3.36/0.97  ------ Input Options
% 3.36/0.97  
% 3.36/0.97  --out_options                           all
% 3.36/0.97  --tptp_safe_out                         true
% 3.36/0.97  --problem_path                          ""
% 3.36/0.97  --include_path                          ""
% 3.36/0.97  --clausifier                            res/vclausify_rel
% 3.36/0.97  --clausifier_options                    --mode clausify
% 3.36/0.97  --stdin                                 false
% 3.36/0.97  --stats_out                             all
% 3.36/0.97  
% 3.36/0.97  ------ General Options
% 3.36/0.97  
% 3.36/0.97  --fof                                   false
% 3.36/0.97  --time_out_real                         305.
% 3.36/0.97  --time_out_virtual                      -1.
% 3.36/0.97  --symbol_type_check                     false
% 3.36/0.97  --clausify_out                          false
% 3.36/0.97  --sig_cnt_out                           false
% 3.36/0.97  --trig_cnt_out                          false
% 3.36/0.97  --trig_cnt_out_tolerance                1.
% 3.36/0.97  --trig_cnt_out_sk_spl                   false
% 3.36/0.97  --abstr_cl_out                          false
% 3.36/0.97  
% 3.36/0.97  ------ Global Options
% 3.36/0.97  
% 3.36/0.97  --schedule                              default
% 3.36/0.97  --add_important_lit                     false
% 3.36/0.97  --prop_solver_per_cl                    1000
% 3.36/0.97  --min_unsat_core                        false
% 3.36/0.97  --soft_assumptions                      false
% 3.36/0.97  --soft_lemma_size                       3
% 3.36/0.97  --prop_impl_unit_size                   0
% 3.36/0.97  --prop_impl_unit                        []
% 3.36/0.97  --share_sel_clauses                     true
% 3.36/0.97  --reset_solvers                         false
% 3.36/0.97  --bc_imp_inh                            [conj_cone]
% 3.36/0.97  --conj_cone_tolerance                   3.
% 3.36/0.97  --extra_neg_conj                        none
% 3.36/0.97  --large_theory_mode                     true
% 3.36/0.97  --prolific_symb_bound                   200
% 3.36/0.97  --lt_threshold                          2000
% 3.36/0.97  --clause_weak_htbl                      true
% 3.36/0.97  --gc_record_bc_elim                     false
% 3.36/0.97  
% 3.36/0.97  ------ Preprocessing Options
% 3.36/0.97  
% 3.36/0.97  --preprocessing_flag                    true
% 3.36/0.97  --time_out_prep_mult                    0.1
% 3.36/0.97  --splitting_mode                        input
% 3.36/0.97  --splitting_grd                         true
% 3.36/0.97  --splitting_cvd                         false
% 3.36/0.97  --splitting_cvd_svl                     false
% 3.36/0.97  --splitting_nvd                         32
% 3.36/0.97  --sub_typing                            true
% 3.36/0.97  --prep_gs_sim                           true
% 3.36/0.97  --prep_unflatten                        true
% 3.36/0.97  --prep_res_sim                          true
% 3.36/0.97  --prep_upred                            true
% 3.36/0.97  --prep_sem_filter                       exhaustive
% 3.36/0.97  --prep_sem_filter_out                   false
% 3.36/0.97  --pred_elim                             true
% 3.36/0.97  --res_sim_input                         true
% 3.36/0.97  --eq_ax_congr_red                       true
% 3.36/0.97  --pure_diseq_elim                       true
% 3.36/0.97  --brand_transform                       false
% 3.36/0.97  --non_eq_to_eq                          false
% 3.36/0.97  --prep_def_merge                        true
% 3.36/0.97  --prep_def_merge_prop_impl              false
% 3.36/0.97  --prep_def_merge_mbd                    true
% 3.36/0.97  --prep_def_merge_tr_red                 false
% 3.36/0.97  --prep_def_merge_tr_cl                  false
% 3.36/0.97  --smt_preprocessing                     true
% 3.36/0.97  --smt_ac_axioms                         fast
% 3.36/0.97  --preprocessed_out                      false
% 3.36/0.97  --preprocessed_stats                    false
% 3.36/0.97  
% 3.36/0.97  ------ Abstraction refinement Options
% 3.36/0.97  
% 3.36/0.97  --abstr_ref                             []
% 3.36/0.97  --abstr_ref_prep                        false
% 3.36/0.97  --abstr_ref_until_sat                   false
% 3.36/0.97  --abstr_ref_sig_restrict                funpre
% 3.36/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.36/0.97  --abstr_ref_under                       []
% 3.36/0.97  
% 3.36/0.97  ------ SAT Options
% 3.36/0.97  
% 3.36/0.97  --sat_mode                              false
% 3.36/0.97  --sat_fm_restart_options                ""
% 3.36/0.97  --sat_gr_def                            false
% 3.36/0.97  --sat_epr_types                         true
% 3.36/0.97  --sat_non_cyclic_types                  false
% 3.36/0.97  --sat_finite_models                     false
% 3.36/0.97  --sat_fm_lemmas                         false
% 3.36/0.97  --sat_fm_prep                           false
% 3.36/0.97  --sat_fm_uc_incr                        true
% 3.36/0.97  --sat_out_model                         small
% 3.36/0.97  --sat_out_clauses                       false
% 3.36/0.97  
% 3.36/0.97  ------ QBF Options
% 3.36/0.97  
% 3.36/0.97  --qbf_mode                              false
% 3.36/0.97  --qbf_elim_univ                         false
% 3.36/0.97  --qbf_dom_inst                          none
% 3.36/0.97  --qbf_dom_pre_inst                      false
% 3.36/0.97  --qbf_sk_in                             false
% 3.36/0.97  --qbf_pred_elim                         true
% 3.36/0.97  --qbf_split                             512
% 3.36/0.97  
% 3.36/0.97  ------ BMC1 Options
% 3.36/0.97  
% 3.36/0.97  --bmc1_incremental                      false
% 3.36/0.97  --bmc1_axioms                           reachable_all
% 3.36/0.97  --bmc1_min_bound                        0
% 3.36/0.97  --bmc1_max_bound                        -1
% 3.36/0.97  --bmc1_max_bound_default                -1
% 3.36/0.97  --bmc1_symbol_reachability              true
% 3.36/0.97  --bmc1_property_lemmas                  false
% 3.36/0.97  --bmc1_k_induction                      false
% 3.36/0.97  --bmc1_non_equiv_states                 false
% 3.36/0.97  --bmc1_deadlock                         false
% 3.36/0.97  --bmc1_ucm                              false
% 3.36/0.97  --bmc1_add_unsat_core                   none
% 3.36/0.97  --bmc1_unsat_core_children              false
% 3.36/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.36/0.97  --bmc1_out_stat                         full
% 3.36/0.97  --bmc1_ground_init                      false
% 3.36/0.97  --bmc1_pre_inst_next_state              false
% 3.36/0.97  --bmc1_pre_inst_state                   false
% 3.36/0.97  --bmc1_pre_inst_reach_state             false
% 3.36/0.97  --bmc1_out_unsat_core                   false
% 3.36/0.97  --bmc1_aig_witness_out                  false
% 3.36/0.97  --bmc1_verbose                          false
% 3.36/0.97  --bmc1_dump_clauses_tptp                false
% 3.36/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.36/0.97  --bmc1_dump_file                        -
% 3.36/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.36/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.36/0.97  --bmc1_ucm_extend_mode                  1
% 3.36/0.97  --bmc1_ucm_init_mode                    2
% 3.36/0.97  --bmc1_ucm_cone_mode                    none
% 3.36/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.36/0.97  --bmc1_ucm_relax_model                  4
% 3.36/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.36/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.36/0.97  --bmc1_ucm_layered_model                none
% 3.36/0.97  --bmc1_ucm_max_lemma_size               10
% 3.36/0.97  
% 3.36/0.97  ------ AIG Options
% 3.36/0.97  
% 3.36/0.97  --aig_mode                              false
% 3.36/0.97  
% 3.36/0.97  ------ Instantiation Options
% 3.36/0.97  
% 3.36/0.97  --instantiation_flag                    true
% 3.36/0.97  --inst_sos_flag                         false
% 3.36/0.97  --inst_sos_phase                        true
% 3.36/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.36/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.36/0.97  --inst_lit_sel_side                     none
% 3.36/0.97  --inst_solver_per_active                1400
% 3.36/0.97  --inst_solver_calls_frac                1.
% 3.36/0.97  --inst_passive_queue_type               priority_queues
% 3.36/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.36/0.97  --inst_passive_queues_freq              [25;2]
% 3.36/0.97  --inst_dismatching                      true
% 3.36/0.97  --inst_eager_unprocessed_to_passive     true
% 3.36/0.97  --inst_prop_sim_given                   true
% 3.36/0.97  --inst_prop_sim_new                     false
% 3.36/0.97  --inst_subs_new                         false
% 3.36/0.97  --inst_eq_res_simp                      false
% 3.36/0.97  --inst_subs_given                       false
% 3.36/0.97  --inst_orphan_elimination               true
% 3.36/0.97  --inst_learning_loop_flag               true
% 3.36/0.97  --inst_learning_start                   3000
% 3.36/0.97  --inst_learning_factor                  2
% 3.36/0.97  --inst_start_prop_sim_after_learn       3
% 3.36/0.97  --inst_sel_renew                        solver
% 3.36/0.97  --inst_lit_activity_flag                true
% 3.36/0.97  --inst_restr_to_given                   false
% 3.36/0.97  --inst_activity_threshold               500
% 3.36/0.97  --inst_out_proof                        true
% 3.36/0.97  
% 3.36/0.97  ------ Resolution Options
% 3.36/0.97  
% 3.36/0.97  --resolution_flag                       false
% 3.36/0.97  --res_lit_sel                           adaptive
% 3.36/0.97  --res_lit_sel_side                      none
% 3.36/0.97  --res_ordering                          kbo
% 3.36/0.97  --res_to_prop_solver                    active
% 3.36/0.97  --res_prop_simpl_new                    false
% 3.36/0.97  --res_prop_simpl_given                  true
% 3.36/0.97  --res_passive_queue_type                priority_queues
% 3.36/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.36/0.97  --res_passive_queues_freq               [15;5]
% 3.36/0.97  --res_forward_subs                      full
% 3.36/0.97  --res_backward_subs                     full
% 3.36/0.97  --res_forward_subs_resolution           true
% 3.36/0.97  --res_backward_subs_resolution          true
% 3.36/0.97  --res_orphan_elimination                true
% 3.36/0.97  --res_time_limit                        2.
% 3.36/0.97  --res_out_proof                         true
% 3.36/0.97  
% 3.36/0.97  ------ Superposition Options
% 3.36/0.97  
% 3.36/0.97  --superposition_flag                    true
% 3.36/0.97  --sup_passive_queue_type                priority_queues
% 3.36/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.36/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.36/0.97  --demod_completeness_check              fast
% 3.36/0.97  --demod_use_ground                      true
% 3.36/0.97  --sup_to_prop_solver                    passive
% 3.36/0.97  --sup_prop_simpl_new                    true
% 3.36/0.97  --sup_prop_simpl_given                  true
% 3.36/0.97  --sup_fun_splitting                     false
% 3.36/0.97  --sup_smt_interval                      50000
% 3.36/0.97  
% 3.36/0.97  ------ Superposition Simplification Setup
% 3.36/0.97  
% 3.36/0.97  --sup_indices_passive                   []
% 3.36/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.36/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.97  --sup_full_bw                           [BwDemod]
% 3.36/0.97  --sup_immed_triv                        [TrivRules]
% 3.36/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.36/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.97  --sup_immed_bw_main                     []
% 3.36/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.36/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/0.97  
% 3.36/0.97  ------ Combination Options
% 3.36/0.97  
% 3.36/0.97  --comb_res_mult                         3
% 3.36/0.97  --comb_sup_mult                         2
% 3.36/0.97  --comb_inst_mult                        10
% 3.36/0.97  
% 3.36/0.97  ------ Debug Options
% 3.36/0.97  
% 3.36/0.97  --dbg_backtrace                         false
% 3.36/0.97  --dbg_dump_prop_clauses                 false
% 3.36/0.97  --dbg_dump_prop_clauses_file            -
% 3.36/0.97  --dbg_out_stat                          false
% 3.36/0.97  
% 3.36/0.97  
% 3.36/0.97  
% 3.36/0.97  
% 3.36/0.97  ------ Proving...
% 3.36/0.97  
% 3.36/0.97  
% 3.36/0.97  % SZS status Theorem for theBenchmark.p
% 3.36/0.97  
% 3.36/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.36/0.97  
% 3.36/0.97  fof(f9,conjecture,(
% 3.36/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 3.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.97  
% 3.36/0.97  fof(f10,negated_conjecture,(
% 3.36/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 3.36/0.97    inference(negated_conjecture,[],[f9])).
% 3.36/0.97  
% 3.36/0.97  fof(f24,plain,(
% 3.36/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.36/0.97    inference(ennf_transformation,[],[f10])).
% 3.36/0.97  
% 3.36/0.97  fof(f25,plain,(
% 3.36/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.36/0.97    inference(flattening,[],[f24])).
% 3.36/0.97  
% 3.36/0.97  fof(f30,plain,(
% 3.36/0.97    ( ! [X2,X0,X3,X1] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,sK4,X3)),k2_tmap_1(X0,X1,sK4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.36/0.97    introduced(choice_axiom,[])).
% 3.36/0.97  
% 3.36/0.97  fof(f29,plain,(
% 3.36/0.97    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,k2_tmap_1(X0,X1,X4,sK3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.36/0.97    introduced(choice_axiom,[])).
% 3.36/0.97  
% 3.36/0.97  fof(f28,plain,(
% 3.36/0.97    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,sK2)) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.36/0.97    introduced(choice_axiom,[])).
% 3.36/0.97  
% 3.36/0.97  fof(f27,plain,(
% 3.36/0.97    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,k2_tmap_1(X0,sK1,X4,X3)),k2_tmap_1(X0,sK1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.36/0.97    introduced(choice_axiom,[])).
% 3.36/0.97  
% 3.36/0.97  fof(f26,plain,(
% 3.36/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,k2_tmap_1(sK0,X1,X4,X3)),k2_tmap_1(sK0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.36/0.97    introduced(choice_axiom,[])).
% 3.36/0.97  
% 3.36/0.97  fof(f31,plain,(
% 3.36/0.97    ((((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.36/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f25,f30,f29,f28,f27,f26])).
% 3.36/0.97  
% 3.36/0.97  fof(f54,plain,(
% 3.36/0.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.36/0.97    inference(cnf_transformation,[],[f31])).
% 3.36/0.97  
% 3.36/0.97  fof(f5,axiom,(
% 3.36/0.97    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 3.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.97  
% 3.36/0.97  fof(f17,plain,(
% 3.36/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 3.36/0.97    inference(ennf_transformation,[],[f5])).
% 3.36/0.97  
% 3.36/0.97  fof(f18,plain,(
% 3.36/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 3.36/0.97    inference(flattening,[],[f17])).
% 3.36/0.97  
% 3.36/0.97  fof(f36,plain,(
% 3.36/0.97    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.36/0.97    inference(cnf_transformation,[],[f18])).
% 3.36/0.97  
% 3.36/0.97  fof(f44,plain,(
% 3.36/0.97    l1_pre_topc(sK0)),
% 3.36/0.97    inference(cnf_transformation,[],[f31])).
% 3.36/0.97  
% 3.36/0.97  fof(f52,plain,(
% 3.36/0.97    v1_funct_1(sK4)),
% 3.36/0.97    inference(cnf_transformation,[],[f31])).
% 3.36/0.97  
% 3.36/0.97  fof(f53,plain,(
% 3.36/0.97    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.36/0.97    inference(cnf_transformation,[],[f31])).
% 3.36/0.97  
% 3.36/0.97  fof(f1,axiom,(
% 3.36/0.97    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.97  
% 3.36/0.97  fof(f11,plain,(
% 3.36/0.97    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.36/0.97    inference(ennf_transformation,[],[f1])).
% 3.36/0.97  
% 3.36/0.97  fof(f32,plain,(
% 3.36/0.97    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.36/0.97    inference(cnf_transformation,[],[f11])).
% 3.36/0.97  
% 3.36/0.97  fof(f47,plain,(
% 3.36/0.97    l1_pre_topc(sK1)),
% 3.36/0.97    inference(cnf_transformation,[],[f31])).
% 3.36/0.97  
% 3.36/0.97  fof(f37,plain,(
% 3.36/0.97    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.36/0.97    inference(cnf_transformation,[],[f18])).
% 3.36/0.97  
% 3.36/0.97  fof(f38,plain,(
% 3.36/0.97    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.36/0.97    inference(cnf_transformation,[],[f18])).
% 3.36/0.97  
% 3.36/0.97  fof(f51,plain,(
% 3.36/0.97    m1_pre_topc(sK3,sK0)),
% 3.36/0.97    inference(cnf_transformation,[],[f31])).
% 3.36/0.97  
% 3.36/0.97  fof(f4,axiom,(
% 3.36/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.97  
% 3.36/0.97  fof(f15,plain,(
% 3.36/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.36/0.97    inference(ennf_transformation,[],[f4])).
% 3.36/0.97  
% 3.36/0.97  fof(f16,plain,(
% 3.36/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.36/0.97    inference(flattening,[],[f15])).
% 3.36/0.97  
% 3.36/0.97  fof(f35,plain,(
% 3.36/0.97    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.36/0.97    inference(cnf_transformation,[],[f16])).
% 3.36/0.97  
% 3.36/0.97  fof(f45,plain,(
% 3.36/0.97    ~v2_struct_0(sK1)),
% 3.36/0.97    inference(cnf_transformation,[],[f31])).
% 3.36/0.97  
% 3.36/0.97  fof(f46,plain,(
% 3.36/0.97    v2_pre_topc(sK1)),
% 3.36/0.97    inference(cnf_transformation,[],[f31])).
% 3.36/0.97  
% 3.36/0.97  fof(f3,axiom,(
% 3.36/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.97  
% 3.36/0.97  fof(f13,plain,(
% 3.36/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.36/0.97    inference(ennf_transformation,[],[f3])).
% 3.36/0.97  
% 3.36/0.97  fof(f14,plain,(
% 3.36/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.36/0.97    inference(flattening,[],[f13])).
% 3.36/0.97  
% 3.36/0.97  fof(f34,plain,(
% 3.36/0.97    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.36/0.97    inference(cnf_transformation,[],[f14])).
% 3.36/0.97  
% 3.36/0.97  fof(f42,plain,(
% 3.36/0.97    ~v2_struct_0(sK0)),
% 3.36/0.97    inference(cnf_transformation,[],[f31])).
% 3.36/0.97  
% 3.36/0.97  fof(f43,plain,(
% 3.36/0.97    v2_pre_topc(sK0)),
% 3.36/0.97    inference(cnf_transformation,[],[f31])).
% 3.36/0.97  
% 3.36/0.97  fof(f6,axiom,(
% 3.36/0.97    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.97  
% 3.36/0.97  fof(f19,plain,(
% 3.36/0.97    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.36/0.97    inference(ennf_transformation,[],[f6])).
% 3.36/0.97  
% 3.36/0.97  fof(f39,plain,(
% 3.36/0.97    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.36/0.97    inference(cnf_transformation,[],[f19])).
% 3.36/0.97  
% 3.36/0.97  fof(f7,axiom,(
% 3.36/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 3.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.97  
% 3.36/0.97  fof(f20,plain,(
% 3.36/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.36/0.97    inference(ennf_transformation,[],[f7])).
% 3.36/0.97  
% 3.36/0.97  fof(f21,plain,(
% 3.36/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.36/0.97    inference(flattening,[],[f20])).
% 3.36/0.97  
% 3.36/0.97  fof(f40,plain,(
% 3.36/0.97    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.36/0.97    inference(cnf_transformation,[],[f21])).
% 3.36/0.97  
% 3.36/0.97  fof(f8,axiom,(
% 3.36/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_pre_topc(X3,X2) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))) => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 3.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.97  
% 3.36/0.97  fof(f22,plain,(
% 3.36/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | (~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.36/0.97    inference(ennf_transformation,[],[f8])).
% 3.36/0.97  
% 3.36/0.97  fof(f23,plain,(
% 3.36/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.36/0.97    inference(flattening,[],[f22])).
% 3.36/0.97  
% 3.36/0.97  fof(f41,plain,(
% 3.36/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.36/0.97    inference(cnf_transformation,[],[f23])).
% 3.36/0.97  
% 3.36/0.97  fof(f50,plain,(
% 3.36/0.97    ~v2_struct_0(sK3)),
% 3.36/0.97    inference(cnf_transformation,[],[f31])).
% 3.36/0.97  
% 3.36/0.97  fof(f48,plain,(
% 3.36/0.97    ~v2_struct_0(sK2)),
% 3.36/0.97    inference(cnf_transformation,[],[f31])).
% 3.36/0.97  
% 3.36/0.97  fof(f49,plain,(
% 3.36/0.97    m1_pre_topc(sK2,sK0)),
% 3.36/0.97    inference(cnf_transformation,[],[f31])).
% 3.36/0.97  
% 3.36/0.97  fof(f55,plain,(
% 3.36/0.97    m1_pre_topc(sK2,sK3)),
% 3.36/0.97    inference(cnf_transformation,[],[f31])).
% 3.36/0.97  
% 3.36/0.97  fof(f56,plain,(
% 3.36/0.97    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))),
% 3.36/0.97    inference(cnf_transformation,[],[f31])).
% 3.36/0.97  
% 3.36/0.97  fof(f2,axiom,(
% 3.36/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.97  
% 3.36/0.97  fof(f12,plain,(
% 3.36/0.97    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.36/0.97    inference(ennf_transformation,[],[f2])).
% 3.36/0.97  
% 3.36/0.97  fof(f33,plain,(
% 3.36/0.97    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.36/0.97    inference(cnf_transformation,[],[f12])).
% 3.36/0.97  
% 3.36/0.97  cnf(c_12,negated_conjecture,
% 3.36/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.36/0.97      inference(cnf_transformation,[],[f54]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_274,negated_conjecture,
% 3.36/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.36/0.97      inference(subtyping,[status(esa)],[c_12]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_736,plain,
% 3.36/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_274]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_6,plain,
% 3.36/0.97      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.36/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.36/0.97      | ~ v1_funct_1(X0)
% 3.36/0.97      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3))
% 3.36/0.97      | ~ l1_struct_0(X3)
% 3.36/0.97      | ~ l1_struct_0(X2)
% 3.36/0.97      | ~ l1_struct_0(X1) ),
% 3.36/0.97      inference(cnf_transformation,[],[f36]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_280,plain,
% 3.36/0.97      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 3.36/0.97      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 3.36/0.97      | ~ v1_funct_1(X0_49)
% 3.36/0.97      | v1_funct_1(k2_tmap_1(X0_48,X1_48,X0_49,X2_48))
% 3.36/0.97      | ~ l1_struct_0(X2_48)
% 3.36/0.97      | ~ l1_struct_0(X1_48)
% 3.36/0.97      | ~ l1_struct_0(X0_48) ),
% 3.36/0.97      inference(subtyping,[status(esa)],[c_6]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_730,plain,
% 3.36/0.97      ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.36/0.97      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 3.36/0.97      | v1_funct_1(X0_49) != iProver_top
% 3.36/0.97      | v1_funct_1(k2_tmap_1(X0_48,X1_48,X0_49,X2_48)) = iProver_top
% 3.36/0.97      | l1_struct_0(X2_48) != iProver_top
% 3.36/0.97      | l1_struct_0(X1_48) != iProver_top
% 3.36/0.97      | l1_struct_0(X0_48) != iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_280]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_1547,plain,
% 3.36/0.97      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.36/0.97      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_48)) = iProver_top
% 3.36/0.97      | v1_funct_1(sK4) != iProver_top
% 3.36/0.97      | l1_struct_0(X0_48) != iProver_top
% 3.36/0.97      | l1_struct_0(sK0) != iProver_top
% 3.36/0.97      | l1_struct_0(sK1) != iProver_top ),
% 3.36/0.97      inference(superposition,[status(thm)],[c_736,c_730]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_22,negated_conjecture,
% 3.36/0.97      ( l1_pre_topc(sK0) ),
% 3.36/0.97      inference(cnf_transformation,[],[f44]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_27,plain,
% 3.36/0.97      ( l1_pre_topc(sK0) = iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_14,negated_conjecture,
% 3.36/0.97      ( v1_funct_1(sK4) ),
% 3.36/0.97      inference(cnf_transformation,[],[f52]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_35,plain,
% 3.36/0.97      ( v1_funct_1(sK4) = iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_13,negated_conjecture,
% 3.36/0.97      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.36/0.97      inference(cnf_transformation,[],[f53]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_36,plain,
% 3.36/0.97      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_0,plain,
% 3.36/0.97      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.36/0.97      inference(cnf_transformation,[],[f32]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_65,plain,
% 3.36/0.97      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_67,plain,
% 3.36/0.97      ( l1_pre_topc(sK0) != iProver_top
% 3.36/0.97      | l1_struct_0(sK0) = iProver_top ),
% 3.36/0.97      inference(instantiation,[status(thm)],[c_65]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_19,negated_conjecture,
% 3.36/0.97      ( l1_pre_topc(sK1) ),
% 3.36/0.97      inference(cnf_transformation,[],[f47]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_267,negated_conjecture,
% 3.36/0.97      ( l1_pre_topc(sK1) ),
% 3.36/0.97      inference(subtyping,[status(esa)],[c_19]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_743,plain,
% 3.36/0.97      ( l1_pre_topc(sK1) = iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_267]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_286,plain,
% 3.36/0.97      ( ~ l1_pre_topc(X0_48) | l1_struct_0(X0_48) ),
% 3.36/0.97      inference(subtyping,[status(esa)],[c_0]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_724,plain,
% 3.36/0.97      ( l1_pre_topc(X0_48) != iProver_top
% 3.36/0.97      | l1_struct_0(X0_48) = iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_286]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_1200,plain,
% 3.36/0.97      ( l1_struct_0(sK1) = iProver_top ),
% 3.36/0.97      inference(superposition,[status(thm)],[c_743,c_724]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_1833,plain,
% 3.36/0.97      ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_48)) = iProver_top
% 3.36/0.97      | l1_struct_0(X0_48) != iProver_top ),
% 3.36/0.97      inference(global_propositional_subsumption,
% 3.36/0.97                [status(thm)],
% 3.36/0.97                [c_1547,c_27,c_35,c_36,c_67,c_1200]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_5,plain,
% 3.36/0.97      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.36/0.97      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 3.36/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.36/0.97      | ~ v1_funct_1(X0)
% 3.36/0.97      | ~ l1_struct_0(X3)
% 3.36/0.97      | ~ l1_struct_0(X2)
% 3.36/0.97      | ~ l1_struct_0(X1) ),
% 3.36/0.97      inference(cnf_transformation,[],[f37]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_281,plain,
% 3.36/0.97      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 3.36/0.97      | v1_funct_2(k2_tmap_1(X0_48,X1_48,X0_49,X2_48),u1_struct_0(X2_48),u1_struct_0(X1_48))
% 3.36/0.97      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 3.36/0.97      | ~ v1_funct_1(X0_49)
% 3.36/0.97      | ~ l1_struct_0(X2_48)
% 3.36/0.97      | ~ l1_struct_0(X1_48)
% 3.36/0.97      | ~ l1_struct_0(X0_48) ),
% 3.36/0.97      inference(subtyping,[status(esa)],[c_5]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_729,plain,
% 3.36/0.97      ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.36/0.97      | v1_funct_2(k2_tmap_1(X0_48,X1_48,X0_49,X2_48),u1_struct_0(X2_48),u1_struct_0(X1_48)) = iProver_top
% 3.36/0.97      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 3.36/0.97      | v1_funct_1(X0_49) != iProver_top
% 3.36/0.97      | l1_struct_0(X2_48) != iProver_top
% 3.36/0.97      | l1_struct_0(X1_48) != iProver_top
% 3.36/0.97      | l1_struct_0(X0_48) != iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_4,plain,
% 3.36/0.97      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.36/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.36/0.97      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 3.36/0.97      | ~ v1_funct_1(X0)
% 3.36/0.97      | ~ l1_struct_0(X3)
% 3.36/0.97      | ~ l1_struct_0(X2)
% 3.36/0.97      | ~ l1_struct_0(X1) ),
% 3.36/0.97      inference(cnf_transformation,[],[f38]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_282,plain,
% 3.36/0.97      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 3.36/0.97      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 3.36/0.97      | m1_subset_1(k2_tmap_1(X0_48,X1_48,X0_49,X2_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48))))
% 3.36/0.97      | ~ v1_funct_1(X0_49)
% 3.36/0.97      | ~ l1_struct_0(X2_48)
% 3.36/0.97      | ~ l1_struct_0(X1_48)
% 3.36/0.97      | ~ l1_struct_0(X0_48) ),
% 3.36/0.97      inference(subtyping,[status(esa)],[c_4]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_728,plain,
% 3.36/0.97      ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.36/0.97      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 3.36/0.97      | m1_subset_1(k2_tmap_1(X0_48,X1_48,X0_49,X2_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48)))) = iProver_top
% 3.36/0.97      | v1_funct_1(X0_49) != iProver_top
% 3.36/0.97      | l1_struct_0(X2_48) != iProver_top
% 3.36/0.97      | l1_struct_0(X1_48) != iProver_top
% 3.36/0.97      | l1_struct_0(X0_48) != iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_15,negated_conjecture,
% 3.36/0.97      ( m1_pre_topc(sK3,sK0) ),
% 3.36/0.97      inference(cnf_transformation,[],[f51]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_271,negated_conjecture,
% 3.36/0.97      ( m1_pre_topc(sK3,sK0) ),
% 3.36/0.97      inference(subtyping,[status(esa)],[c_15]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_739,plain,
% 3.36/0.97      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_271]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_3,plain,
% 3.36/0.97      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.36/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.36/0.97      | ~ m1_pre_topc(X3,X4)
% 3.36/0.97      | ~ m1_pre_topc(X3,X1)
% 3.36/0.97      | ~ m1_pre_topc(X1,X4)
% 3.36/0.97      | v2_struct_0(X4)
% 3.36/0.97      | v2_struct_0(X2)
% 3.36/0.97      | ~ v2_pre_topc(X2)
% 3.36/0.97      | ~ v2_pre_topc(X4)
% 3.36/0.97      | ~ v1_funct_1(X0)
% 3.36/0.97      | ~ l1_pre_topc(X4)
% 3.36/0.97      | ~ l1_pre_topc(X2)
% 3.36/0.97      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 3.36/0.97      inference(cnf_transformation,[],[f35]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_283,plain,
% 3.36/0.97      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 3.36/0.97      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 3.36/0.97      | ~ m1_pre_topc(X0_48,X2_48)
% 3.36/0.97      | ~ m1_pre_topc(X3_48,X2_48)
% 3.36/0.97      | ~ m1_pre_topc(X3_48,X0_48)
% 3.36/0.97      | v2_struct_0(X2_48)
% 3.36/0.97      | v2_struct_0(X1_48)
% 3.36/0.97      | ~ v2_pre_topc(X1_48)
% 3.36/0.97      | ~ v2_pre_topc(X2_48)
% 3.36/0.97      | ~ v1_funct_1(X0_49)
% 3.36/0.97      | ~ l1_pre_topc(X2_48)
% 3.36/0.97      | ~ l1_pre_topc(X1_48)
% 3.36/0.97      | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X3_48)) = k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49) ),
% 3.36/0.97      inference(subtyping,[status(esa)],[c_3]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_727,plain,
% 3.36/0.97      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49)
% 3.36/0.97      | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.36/0.97      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 3.36/0.97      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 3.36/0.97      | m1_pre_topc(X0_48,X3_48) != iProver_top
% 3.36/0.97      | m1_pre_topc(X2_48,X3_48) != iProver_top
% 3.36/0.97      | v2_struct_0(X1_48) = iProver_top
% 3.36/0.97      | v2_struct_0(X3_48) = iProver_top
% 3.36/0.97      | v2_pre_topc(X1_48) != iProver_top
% 3.36/0.97      | v2_pre_topc(X3_48) != iProver_top
% 3.36/0.97      | v1_funct_1(X0_49) != iProver_top
% 3.36/0.97      | l1_pre_topc(X1_48) != iProver_top
% 3.36/0.97      | l1_pre_topc(X3_48) != iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_2211,plain,
% 3.36/0.97      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK0,X0_48,sK4)
% 3.36/0.97      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.36/0.97      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.36/0.97      | m1_pre_topc(X0_48,sK0) != iProver_top
% 3.36/0.97      | m1_pre_topc(sK0,X1_48) != iProver_top
% 3.36/0.97      | v2_struct_0(X1_48) = iProver_top
% 3.36/0.97      | v2_struct_0(sK1) = iProver_top
% 3.36/0.97      | v2_pre_topc(X1_48) != iProver_top
% 3.36/0.97      | v2_pre_topc(sK1) != iProver_top
% 3.36/0.97      | v1_funct_1(sK4) != iProver_top
% 3.36/0.97      | l1_pre_topc(X1_48) != iProver_top
% 3.36/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.36/0.97      inference(superposition,[status(thm)],[c_736,c_727]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_21,negated_conjecture,
% 3.36/0.97      ( ~ v2_struct_0(sK1) ),
% 3.36/0.97      inference(cnf_transformation,[],[f45]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_28,plain,
% 3.36/0.97      ( v2_struct_0(sK1) != iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_20,negated_conjecture,
% 3.36/0.97      ( v2_pre_topc(sK1) ),
% 3.36/0.97      inference(cnf_transformation,[],[f46]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_29,plain,
% 3.36/0.97      ( v2_pre_topc(sK1) = iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_30,plain,
% 3.36/0.97      ( l1_pre_topc(sK1) = iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_2443,plain,
% 3.36/0.97      ( l1_pre_topc(X1_48) != iProver_top
% 3.36/0.97      | v2_pre_topc(X1_48) != iProver_top
% 3.36/0.97      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK0,X0_48,sK4)
% 3.36/0.97      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.36/0.97      | m1_pre_topc(X0_48,sK0) != iProver_top
% 3.36/0.97      | m1_pre_topc(sK0,X1_48) != iProver_top
% 3.36/0.97      | v2_struct_0(X1_48) = iProver_top ),
% 3.36/0.97      inference(global_propositional_subsumption,
% 3.36/0.97                [status(thm)],
% 3.36/0.97                [c_2211,c_28,c_29,c_30,c_35,c_36]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_2444,plain,
% 3.36/0.97      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK0,X0_48,sK4)
% 3.36/0.97      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.36/0.97      | m1_pre_topc(X0_48,sK0) != iProver_top
% 3.36/0.97      | m1_pre_topc(sK0,X1_48) != iProver_top
% 3.36/0.97      | v2_struct_0(X1_48) = iProver_top
% 3.36/0.97      | v2_pre_topc(X1_48) != iProver_top
% 3.36/0.97      | l1_pre_topc(X1_48) != iProver_top ),
% 3.36/0.97      inference(renaming,[status(thm)],[c_2443]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_2457,plain,
% 3.36/0.97      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
% 3.36/0.97      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.36/0.97      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.36/0.97      | v2_struct_0(sK0) = iProver_top
% 3.36/0.97      | v2_pre_topc(sK0) != iProver_top
% 3.36/0.97      | l1_pre_topc(sK0) != iProver_top ),
% 3.36/0.97      inference(superposition,[status(thm)],[c_739,c_2444]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_2,plain,
% 3.36/0.97      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.36/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.36/0.97      | ~ m1_pre_topc(X3,X1)
% 3.36/0.97      | v2_struct_0(X1)
% 3.36/0.97      | v2_struct_0(X2)
% 3.36/0.97      | ~ v2_pre_topc(X2)
% 3.36/0.97      | ~ v2_pre_topc(X1)
% 3.36/0.97      | ~ v1_funct_1(X0)
% 3.36/0.97      | ~ l1_pre_topc(X1)
% 3.36/0.97      | ~ l1_pre_topc(X2)
% 3.36/0.97      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.36/0.97      inference(cnf_transformation,[],[f34]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_284,plain,
% 3.36/0.97      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 3.36/0.97      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 3.36/0.97      | ~ m1_pre_topc(X2_48,X0_48)
% 3.36/0.97      | v2_struct_0(X1_48)
% 3.36/0.97      | v2_struct_0(X0_48)
% 3.36/0.97      | ~ v2_pre_topc(X1_48)
% 3.36/0.97      | ~ v2_pre_topc(X0_48)
% 3.36/0.97      | ~ v1_funct_1(X0_49)
% 3.36/0.97      | ~ l1_pre_topc(X1_48)
% 3.36/0.97      | ~ l1_pre_topc(X0_48)
% 3.36/0.97      | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k2_tmap_1(X0_48,X1_48,X0_49,X2_48) ),
% 3.36/0.97      inference(subtyping,[status(esa)],[c_2]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_726,plain,
% 3.36/0.97      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k2_tmap_1(X0_48,X1_48,X0_49,X2_48)
% 3.36/0.97      | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.36/0.97      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 3.36/0.97      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 3.36/0.97      | v2_struct_0(X1_48) = iProver_top
% 3.36/0.97      | v2_struct_0(X0_48) = iProver_top
% 3.36/0.97      | v2_pre_topc(X1_48) != iProver_top
% 3.36/0.97      | v2_pre_topc(X0_48) != iProver_top
% 3.36/0.97      | v1_funct_1(X0_49) != iProver_top
% 3.36/0.97      | l1_pre_topc(X1_48) != iProver_top
% 3.36/0.97      | l1_pre_topc(X0_48) != iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_284]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_1509,plain,
% 3.36/0.97      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k2_tmap_1(sK0,sK1,sK4,X0_48)
% 3.36/0.97      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.36/0.97      | m1_pre_topc(X0_48,sK0) != iProver_top
% 3.36/0.97      | v2_struct_0(sK0) = iProver_top
% 3.36/0.97      | v2_struct_0(sK1) = iProver_top
% 3.36/0.97      | v2_pre_topc(sK0) != iProver_top
% 3.36/0.97      | v2_pre_topc(sK1) != iProver_top
% 3.36/0.97      | v1_funct_1(sK4) != iProver_top
% 3.36/0.97      | l1_pre_topc(sK0) != iProver_top
% 3.36/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.36/0.97      inference(superposition,[status(thm)],[c_736,c_726]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_24,negated_conjecture,
% 3.36/0.97      ( ~ v2_struct_0(sK0) ),
% 3.36/0.97      inference(cnf_transformation,[],[f42]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_25,plain,
% 3.36/0.97      ( v2_struct_0(sK0) != iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_23,negated_conjecture,
% 3.36/0.97      ( v2_pre_topc(sK0) ),
% 3.36/0.97      inference(cnf_transformation,[],[f43]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_26,plain,
% 3.36/0.97      ( v2_pre_topc(sK0) = iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_2052,plain,
% 3.36/0.97      ( m1_pre_topc(X0_48,sK0) != iProver_top
% 3.36/0.97      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k2_tmap_1(sK0,sK1,sK4,X0_48) ),
% 3.36/0.97      inference(global_propositional_subsumption,
% 3.36/0.97                [status(thm)],
% 3.36/0.97                [c_1509,c_25,c_26,c_27,c_28,c_29,c_30,c_35,c_36]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_2053,plain,
% 3.36/0.97      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k2_tmap_1(sK0,sK1,sK4,X0_48)
% 3.36/0.97      | m1_pre_topc(X0_48,sK0) != iProver_top ),
% 3.36/0.97      inference(renaming,[status(thm)],[c_2052]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_2060,plain,
% 3.36/0.97      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 3.36/0.97      inference(superposition,[status(thm)],[c_739,c_2053]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_2491,plain,
% 3.36/0.97      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
% 3.36/0.97      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.36/0.97      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.36/0.97      | v2_struct_0(sK0) = iProver_top
% 3.36/0.97      | v2_pre_topc(sK0) != iProver_top
% 3.36/0.97      | l1_pre_topc(sK0) != iProver_top ),
% 3.36/0.97      inference(light_normalisation,[status(thm)],[c_2457,c_2060]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_34,plain,
% 3.36/0.97      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_7,plain,
% 3.36/0.97      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.36/0.97      inference(cnf_transformation,[],[f39]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_46,plain,
% 3.36/0.97      ( m1_pre_topc(X0,X0) = iProver_top
% 3.36/0.97      | l1_pre_topc(X0) != iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_48,plain,
% 3.36/0.97      ( m1_pre_topc(sK0,sK0) = iProver_top
% 3.36/0.97      | l1_pre_topc(sK0) != iProver_top ),
% 3.36/0.97      inference(instantiation,[status(thm)],[c_46]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_2799,plain,
% 3.36/0.97      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 3.36/0.97      inference(global_propositional_subsumption,
% 3.36/0.97                [status(thm)],
% 3.36/0.97                [c_2491,c_25,c_26,c_27,c_34,c_48]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_279,plain,
% 3.36/0.97      ( m1_pre_topc(X0_48,X0_48) | ~ l1_pre_topc(X0_48) ),
% 3.36/0.97      inference(subtyping,[status(esa)],[c_7]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_731,plain,
% 3.36/0.97      ( m1_pre_topc(X0_48,X0_48) = iProver_top
% 3.36/0.97      | l1_pre_topc(X0_48) != iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_279]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_2459,plain,
% 3.36/0.97      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k3_tmap_1(X0_48,sK1,sK0,X0_48,sK4)
% 3.36/0.97      | m1_pre_topc(X0_48,sK0) != iProver_top
% 3.36/0.97      | m1_pre_topc(sK0,X0_48) != iProver_top
% 3.36/0.97      | v2_struct_0(X0_48) = iProver_top
% 3.36/0.97      | v2_pre_topc(X0_48) != iProver_top
% 3.36/0.97      | l1_pre_topc(X0_48) != iProver_top ),
% 3.36/0.97      inference(superposition,[status(thm)],[c_731,c_2444]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_2524,plain,
% 3.36/0.97      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k3_tmap_1(sK0,sK1,sK0,sK0,sK4)
% 3.36/0.97      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.36/0.97      | v2_struct_0(sK0) = iProver_top
% 3.36/0.97      | v2_pre_topc(sK0) != iProver_top
% 3.36/0.97      | l1_pre_topc(sK0) != iProver_top ),
% 3.36/0.97      inference(superposition,[status(thm)],[c_731,c_2459]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_2062,plain,
% 3.36/0.97      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0)
% 3.36/0.97      | l1_pre_topc(sK0) != iProver_top ),
% 3.36/0.97      inference(superposition,[status(thm)],[c_731,c_2053]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_47,plain,
% 3.36/0.97      ( m1_pre_topc(sK0,sK0) | ~ l1_pre_topc(sK0) ),
% 3.36/0.97      inference(instantiation,[status(thm)],[c_7]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_1028,plain,
% 3.36/0.97      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.36/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.36/0.97      | ~ m1_pre_topc(X0_48,sK0)
% 3.36/0.97      | v2_struct_0(sK0)
% 3.36/0.97      | v2_struct_0(sK1)
% 3.36/0.97      | ~ v2_pre_topc(sK0)
% 3.36/0.97      | ~ v2_pre_topc(sK1)
% 3.36/0.97      | ~ v1_funct_1(sK4)
% 3.36/0.97      | ~ l1_pre_topc(sK0)
% 3.36/0.97      | ~ l1_pre_topc(sK1)
% 3.36/0.97      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k2_tmap_1(sK0,sK1,sK4,X0_48) ),
% 3.36/0.97      inference(instantiation,[status(thm)],[c_284]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_1030,plain,
% 3.36/0.97      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.36/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.36/0.97      | ~ m1_pre_topc(sK0,sK0)
% 3.36/0.97      | v2_struct_0(sK0)
% 3.36/0.97      | v2_struct_0(sK1)
% 3.36/0.97      | ~ v2_pre_topc(sK0)
% 3.36/0.97      | ~ v2_pre_topc(sK1)
% 3.36/0.97      | ~ v1_funct_1(sK4)
% 3.36/0.97      | ~ l1_pre_topc(sK0)
% 3.36/0.97      | ~ l1_pre_topc(sK1)
% 3.36/0.97      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0) ),
% 3.36/0.97      inference(instantiation,[status(thm)],[c_1028]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_2374,plain,
% 3.36/0.97      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0) ),
% 3.36/0.97      inference(global_propositional_subsumption,
% 3.36/0.97                [status(thm)],
% 3.36/0.97                [c_2062,c_24,c_23,c_22,c_21,c_20,c_19,c_14,c_13,c_12,
% 3.36/0.97                 c_47,c_1030]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_2530,plain,
% 3.36/0.97      ( k3_tmap_1(sK0,sK1,sK0,sK0,sK4) = k2_tmap_1(sK0,sK1,sK4,sK0)
% 3.36/0.97      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.36/0.97      | v2_struct_0(sK0) = iProver_top
% 3.36/0.97      | v2_pre_topc(sK0) != iProver_top
% 3.36/0.97      | l1_pre_topc(sK0) != iProver_top ),
% 3.36/0.97      inference(light_normalisation,[status(thm)],[c_2524,c_2374]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_2977,plain,
% 3.36/0.97      ( k3_tmap_1(sK0,sK1,sK0,sK0,sK4) = k2_tmap_1(sK0,sK1,sK4,sK0) ),
% 3.36/0.97      inference(global_propositional_subsumption,
% 3.36/0.97                [status(thm)],
% 3.36/0.97                [c_2530,c_25,c_26,c_27,c_48]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_8,plain,
% 3.36/0.97      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
% 3.36/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.36/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.36/0.97      | ~ m1_pre_topc(X0,X3)
% 3.36/0.97      | v2_struct_0(X3)
% 3.36/0.97      | v2_struct_0(X1)
% 3.36/0.97      | v2_struct_0(X0)
% 3.36/0.97      | ~ v2_pre_topc(X1)
% 3.36/0.97      | ~ v2_pre_topc(X3)
% 3.36/0.97      | ~ v1_funct_1(X2)
% 3.36/0.97      | ~ l1_pre_topc(X3)
% 3.36/0.97      | ~ l1_pre_topc(X1) ),
% 3.36/0.97      inference(cnf_transformation,[],[f40]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_278,plain,
% 3.36/0.97      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,k3_tmap_1(X2_48,X1_48,X0_48,X0_48,X0_49))
% 3.36/0.97      | ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 3.36/0.97      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 3.36/0.97      | ~ m1_pre_topc(X0_48,X2_48)
% 3.36/0.97      | v2_struct_0(X1_48)
% 3.36/0.97      | v2_struct_0(X0_48)
% 3.36/0.97      | v2_struct_0(X2_48)
% 3.36/0.97      | ~ v2_pre_topc(X1_48)
% 3.36/0.97      | ~ v2_pre_topc(X2_48)
% 3.36/0.97      | ~ v1_funct_1(X0_49)
% 3.36/0.97      | ~ l1_pre_topc(X1_48)
% 3.36/0.97      | ~ l1_pre_topc(X2_48) ),
% 3.36/0.97      inference(subtyping,[status(esa)],[c_8]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_732,plain,
% 3.36/0.97      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,k3_tmap_1(X2_48,X1_48,X0_48,X0_48,X0_49)) = iProver_top
% 3.36/0.97      | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.36/0.97      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 3.36/0.97      | m1_pre_topc(X0_48,X2_48) != iProver_top
% 3.36/0.97      | v2_struct_0(X1_48) = iProver_top
% 3.36/0.97      | v2_struct_0(X0_48) = iProver_top
% 3.36/0.97      | v2_struct_0(X2_48) = iProver_top
% 3.36/0.97      | v2_pre_topc(X1_48) != iProver_top
% 3.36/0.97      | v2_pre_topc(X2_48) != iProver_top
% 3.36/0.97      | v1_funct_1(X0_49) != iProver_top
% 3.36/0.97      | l1_pre_topc(X1_48) != iProver_top
% 3.36/0.97      | l1_pre_topc(X2_48) != iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_278]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_2980,plain,
% 3.36/0.97      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) = iProver_top
% 3.36/0.97      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.36/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.36/0.97      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.36/0.97      | v2_struct_0(sK0) = iProver_top
% 3.36/0.97      | v2_struct_0(sK1) = iProver_top
% 3.36/0.97      | v2_pre_topc(sK0) != iProver_top
% 3.36/0.97      | v2_pre_topc(sK1) != iProver_top
% 3.36/0.97      | v1_funct_1(sK4) != iProver_top
% 3.36/0.97      | l1_pre_topc(sK0) != iProver_top
% 3.36/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.36/0.97      inference(superposition,[status(thm)],[c_2977,c_732]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_37,plain,
% 3.36/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_3118,plain,
% 3.36/0.97      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) = iProver_top ),
% 3.36/0.97      inference(global_propositional_subsumption,
% 3.36/0.97                [status(thm)],
% 3.36/0.97                [c_2980,c_25,c_26,c_27,c_28,c_29,c_30,c_35,c_36,c_37,
% 3.36/0.97                 c_48]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_9,plain,
% 3.36/0.97      ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_tmap_1(X3,X1,X4,X0))
% 3.36/0.97      | r2_funct_2(u1_struct_0(X5),u1_struct_0(X1),k3_tmap_1(X3,X1,X0,X5,X2),k2_tmap_1(X3,X1,X4,X5))
% 3.36/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.36/0.97      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
% 3.36/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.36/0.97      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.36/0.97      | ~ m1_pre_topc(X5,X3)
% 3.36/0.97      | ~ m1_pre_topc(X5,X0)
% 3.36/0.97      | ~ m1_pre_topc(X0,X3)
% 3.36/0.97      | v2_struct_0(X3)
% 3.36/0.97      | v2_struct_0(X1)
% 3.36/0.97      | v2_struct_0(X0)
% 3.36/0.97      | v2_struct_0(X5)
% 3.36/0.97      | ~ v2_pre_topc(X1)
% 3.36/0.97      | ~ v2_pre_topc(X3)
% 3.36/0.97      | ~ v1_funct_1(X4)
% 3.36/0.97      | ~ v1_funct_1(X2)
% 3.36/0.97      | ~ l1_pre_topc(X3)
% 3.36/0.97      | ~ l1_pre_topc(X1) ),
% 3.36/0.97      inference(cnf_transformation,[],[f41]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_277,plain,
% 3.36/0.97      ( ~ r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,k2_tmap_1(X2_48,X1_48,X1_49,X0_48))
% 3.36/0.97      | r2_funct_2(u1_struct_0(X3_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k2_tmap_1(X2_48,X1_48,X1_49,X3_48))
% 3.36/0.97      | ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 3.36/0.97      | ~ v1_funct_2(X1_49,u1_struct_0(X2_48),u1_struct_0(X1_48))
% 3.36/0.97      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 3.36/0.97      | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48))))
% 3.36/0.97      | ~ m1_pre_topc(X3_48,X2_48)
% 3.36/0.97      | ~ m1_pre_topc(X3_48,X0_48)
% 3.36/0.97      | ~ m1_pre_topc(X0_48,X2_48)
% 3.36/0.97      | v2_struct_0(X3_48)
% 3.36/0.97      | v2_struct_0(X1_48)
% 3.36/0.97      | v2_struct_0(X0_48)
% 3.36/0.97      | v2_struct_0(X2_48)
% 3.36/0.97      | ~ v2_pre_topc(X1_48)
% 3.36/0.97      | ~ v2_pre_topc(X2_48)
% 3.36/0.97      | ~ v1_funct_1(X1_49)
% 3.36/0.97      | ~ v1_funct_1(X0_49)
% 3.36/0.97      | ~ l1_pre_topc(X1_48)
% 3.36/0.97      | ~ l1_pre_topc(X2_48) ),
% 3.36/0.97      inference(subtyping,[status(esa)],[c_9]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_733,plain,
% 3.36/0.97      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,k2_tmap_1(X2_48,X1_48,X1_49,X0_48)) != iProver_top
% 3.36/0.97      | r2_funct_2(u1_struct_0(X3_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k2_tmap_1(X2_48,X1_48,X1_49,X3_48)) = iProver_top
% 3.36/0.97      | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.36/0.97      | v1_funct_2(X1_49,u1_struct_0(X2_48),u1_struct_0(X1_48)) != iProver_top
% 3.36/0.97      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 3.36/0.97      | m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48)))) != iProver_top
% 3.36/0.97      | m1_pre_topc(X3_48,X0_48) != iProver_top
% 3.36/0.97      | m1_pre_topc(X0_48,X2_48) != iProver_top
% 3.36/0.97      | m1_pre_topc(X3_48,X2_48) != iProver_top
% 3.36/0.97      | v2_struct_0(X3_48) = iProver_top
% 3.36/0.97      | v2_struct_0(X1_48) = iProver_top
% 3.36/0.97      | v2_struct_0(X0_48) = iProver_top
% 3.36/0.97      | v2_struct_0(X2_48) = iProver_top
% 3.36/0.97      | v2_pre_topc(X1_48) != iProver_top
% 3.36/0.97      | v2_pre_topc(X2_48) != iProver_top
% 3.36/0.97      | v1_funct_1(X0_49) != iProver_top
% 3.36/0.97      | v1_funct_1(X1_49) != iProver_top
% 3.36/0.97      | l1_pre_topc(X1_48) != iProver_top
% 3.36/0.97      | l1_pre_topc(X2_48) != iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_277]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_3123,plain,
% 3.36/0.97      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_48,sK4),k2_tmap_1(sK0,sK1,sK4,X0_48)) = iProver_top
% 3.36/0.97      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.36/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.36/0.97      | m1_pre_topc(X0_48,sK0) != iProver_top
% 3.36/0.97      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.36/0.97      | v2_struct_0(X0_48) = iProver_top
% 3.36/0.97      | v2_struct_0(sK0) = iProver_top
% 3.36/0.97      | v2_struct_0(sK1) = iProver_top
% 3.36/0.97      | v2_pre_topc(sK0) != iProver_top
% 3.36/0.97      | v2_pre_topc(sK1) != iProver_top
% 3.36/0.97      | v1_funct_1(sK4) != iProver_top
% 3.36/0.97      | l1_pre_topc(sK0) != iProver_top
% 3.36/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.36/0.97      inference(superposition,[status(thm)],[c_3118,c_733]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_3128,plain,
% 3.36/0.97      ( v2_struct_0(X0_48) = iProver_top
% 3.36/0.97      | r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_48,sK4),k2_tmap_1(sK0,sK1,sK4,X0_48)) = iProver_top
% 3.36/0.97      | m1_pre_topc(X0_48,sK0) != iProver_top ),
% 3.36/0.97      inference(global_propositional_subsumption,
% 3.36/0.97                [status(thm)],
% 3.36/0.97                [c_3123,c_25,c_26,c_27,c_28,c_29,c_30,c_35,c_36,c_37,
% 3.36/0.97                 c_48]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_3129,plain,
% 3.36/0.97      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_48,sK4),k2_tmap_1(sK0,sK1,sK4,X0_48)) = iProver_top
% 3.36/0.97      | m1_pre_topc(X0_48,sK0) != iProver_top
% 3.36/0.97      | v2_struct_0(X0_48) = iProver_top ),
% 3.36/0.97      inference(renaming,[status(thm)],[c_3128]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_3138,plain,
% 3.36/0.97      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top
% 3.36/0.97      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.36/0.97      | v2_struct_0(sK3) = iProver_top ),
% 3.36/0.97      inference(superposition,[status(thm)],[c_2799,c_3129]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_16,negated_conjecture,
% 3.36/0.97      ( ~ v2_struct_0(sK3) ),
% 3.36/0.97      inference(cnf_transformation,[],[f50]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_33,plain,
% 3.36/0.97      ( v2_struct_0(sK3) != iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_4598,plain,
% 3.36/0.97      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
% 3.36/0.97      inference(global_propositional_subsumption,
% 3.36/0.97                [status(thm)],
% 3.36/0.97                [c_3138,c_33,c_34]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_4603,plain,
% 3.36/0.97      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,X0_48,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,X0_48)) = iProver_top
% 3.36/0.97      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.36/0.97      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.36/0.97      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.36/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.36/0.97      | m1_pre_topc(X0_48,sK3) != iProver_top
% 3.36/0.97      | m1_pre_topc(X0_48,sK0) != iProver_top
% 3.36/0.97      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.36/0.97      | v2_struct_0(X0_48) = iProver_top
% 3.36/0.97      | v2_struct_0(sK3) = iProver_top
% 3.36/0.97      | v2_struct_0(sK0) = iProver_top
% 3.36/0.97      | v2_struct_0(sK1) = iProver_top
% 3.36/0.97      | v2_pre_topc(sK0) != iProver_top
% 3.36/0.97      | v2_pre_topc(sK1) != iProver_top
% 3.36/0.97      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 3.36/0.97      | v1_funct_1(sK4) != iProver_top
% 3.36/0.97      | l1_pre_topc(sK0) != iProver_top
% 3.36/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.36/0.97      inference(superposition,[status(thm)],[c_4598,c_733]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_18,negated_conjecture,
% 3.36/0.97      ( ~ v2_struct_0(sK2) ),
% 3.36/0.97      inference(cnf_transformation,[],[f48]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_31,plain,
% 3.36/0.97      ( v2_struct_0(sK2) != iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_17,negated_conjecture,
% 3.36/0.97      ( m1_pre_topc(sK2,sK0) ),
% 3.36/0.97      inference(cnf_transformation,[],[f49]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_32,plain,
% 3.36/0.97      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_11,negated_conjecture,
% 3.36/0.97      ( m1_pre_topc(sK2,sK3) ),
% 3.36/0.97      inference(cnf_transformation,[],[f55]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_38,plain,
% 3.36/0.97      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_10,negated_conjecture,
% 3.36/0.97      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) ),
% 3.36/0.97      inference(cnf_transformation,[],[f56]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_39,plain,
% 3.36/0.97      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_1143,plain,
% 3.36/0.97      ( ~ r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49,k2_tmap_1(X1_48,sK1,X1_49,X0_48))
% 3.36/0.97      | r2_funct_2(u1_struct_0(X2_48),u1_struct_0(sK1),k3_tmap_1(X1_48,sK1,X0_48,X2_48,X0_49),k2_tmap_1(X1_48,sK1,X1_49,X2_48))
% 3.36/0.97      | ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(sK1))
% 3.36/0.97      | ~ v1_funct_2(X1_49,u1_struct_0(X1_48),u1_struct_0(sK1))
% 3.36/0.97      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(sK1))))
% 3.36/0.97      | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_48),u1_struct_0(sK1))))
% 3.36/0.97      | ~ m1_pre_topc(X2_48,X0_48)
% 3.36/0.97      | ~ m1_pre_topc(X0_48,X1_48)
% 3.36/0.97      | ~ m1_pre_topc(X2_48,X1_48)
% 3.36/0.97      | v2_struct_0(X1_48)
% 3.36/0.97      | v2_struct_0(X0_48)
% 3.36/0.97      | v2_struct_0(X2_48)
% 3.36/0.97      | v2_struct_0(sK1)
% 3.36/0.97      | ~ v2_pre_topc(X1_48)
% 3.36/0.97      | ~ v2_pre_topc(sK1)
% 3.36/0.97      | ~ v1_funct_1(X1_49)
% 3.36/0.97      | ~ v1_funct_1(X0_49)
% 3.36/0.97      | ~ l1_pre_topc(X1_48)
% 3.36/0.97      | ~ l1_pre_topc(sK1) ),
% 3.36/0.97      inference(instantiation,[status(thm)],[c_277]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_6103,plain,
% 3.36/0.97      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3))
% 3.36/0.97      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
% 3.36/0.97      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.36/0.97      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.36/0.97      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.36/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.36/0.97      | ~ m1_pre_topc(sK3,sK0)
% 3.36/0.97      | ~ m1_pre_topc(sK2,sK3)
% 3.36/0.97      | ~ m1_pre_topc(sK2,sK0)
% 3.36/0.97      | v2_struct_0(sK3)
% 3.36/0.97      | v2_struct_0(sK0)
% 3.36/0.97      | v2_struct_0(sK1)
% 3.36/0.97      | v2_struct_0(sK2)
% 3.36/0.97      | ~ v2_pre_topc(sK0)
% 3.36/0.97      | ~ v2_pre_topc(sK1)
% 3.36/0.97      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
% 3.36/0.97      | ~ v1_funct_1(sK4)
% 3.36/0.97      | ~ l1_pre_topc(sK0)
% 3.36/0.97      | ~ l1_pre_topc(sK1) ),
% 3.36/0.97      inference(instantiation,[status(thm)],[c_1143]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_6104,plain,
% 3.36/0.97      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 3.36/0.97      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
% 3.36/0.97      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.36/0.97      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.36/0.97      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.36/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.36/0.97      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.36/0.97      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.36/0.97      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.36/0.97      | v2_struct_0(sK3) = iProver_top
% 3.36/0.97      | v2_struct_0(sK0) = iProver_top
% 3.36/0.97      | v2_struct_0(sK1) = iProver_top
% 3.36/0.97      | v2_struct_0(sK2) = iProver_top
% 3.36/0.97      | v2_pre_topc(sK0) != iProver_top
% 3.36/0.97      | v2_pre_topc(sK1) != iProver_top
% 3.36/0.97      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 3.36/0.97      | v1_funct_1(sK4) != iProver_top
% 3.36/0.97      | l1_pre_topc(sK0) != iProver_top
% 3.36/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_6103]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_8365,plain,
% 3.36/0.97      ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 3.36/0.97      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.36/0.97      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top ),
% 3.36/0.97      inference(global_propositional_subsumption,
% 3.36/0.97                [status(thm)],
% 3.36/0.97                [c_4603,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32,c_33,
% 3.36/0.97                 c_34,c_35,c_36,c_37,c_38,c_39,c_3138,c_6104]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_8366,plain,
% 3.36/0.97      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.36/0.97      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.36/0.97      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 3.36/0.97      inference(renaming,[status(thm)],[c_8365]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_8372,plain,
% 3.36/0.97      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.36/0.97      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.36/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.36/0.97      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 3.36/0.97      | v1_funct_1(sK4) != iProver_top
% 3.36/0.97      | l1_struct_0(sK3) != iProver_top
% 3.36/0.97      | l1_struct_0(sK0) != iProver_top
% 3.36/0.97      | l1_struct_0(sK1) != iProver_top ),
% 3.36/0.97      inference(superposition,[status(thm)],[c_728,c_8366]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_1,plain,
% 3.36/0.97      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.36/0.97      inference(cnf_transformation,[],[f33]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_285,plain,
% 3.36/0.97      ( ~ m1_pre_topc(X0_48,X1_48)
% 3.36/0.97      | ~ l1_pre_topc(X1_48)
% 3.36/0.97      | l1_pre_topc(X0_48) ),
% 3.36/0.97      inference(subtyping,[status(esa)],[c_1]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_725,plain,
% 3.36/0.97      ( m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.36/0.97      | l1_pre_topc(X1_48) != iProver_top
% 3.36/0.97      | l1_pre_topc(X0_48) = iProver_top ),
% 3.36/0.97      inference(predicate_to_equality,[status(thm)],[c_285]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_1358,plain,
% 3.36/0.97      ( l1_pre_topc(sK3) = iProver_top
% 3.36/0.97      | l1_pre_topc(sK0) != iProver_top ),
% 3.36/0.97      inference(superposition,[status(thm)],[c_739,c_725]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_1820,plain,
% 3.36/0.97      ( l1_pre_topc(sK3) = iProver_top ),
% 3.36/0.97      inference(global_propositional_subsumption,
% 3.36/0.97                [status(thm)],
% 3.36/0.97                [c_1358,c_27]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_1825,plain,
% 3.36/0.97      ( l1_struct_0(sK3) = iProver_top ),
% 3.36/0.97      inference(superposition,[status(thm)],[c_1820,c_724]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_8736,plain,
% 3.36/0.97      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.36/0.97      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 3.36/0.97      inference(global_propositional_subsumption,
% 3.36/0.97                [status(thm)],
% 3.36/0.97                [c_8372,c_27,c_35,c_36,c_37,c_67,c_1200,c_1825]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_8742,plain,
% 3.36/0.97      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.36/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.36/0.97      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 3.36/0.97      | v1_funct_1(sK4) != iProver_top
% 3.36/0.97      | l1_struct_0(sK3) != iProver_top
% 3.36/0.97      | l1_struct_0(sK0) != iProver_top
% 3.36/0.97      | l1_struct_0(sK1) != iProver_top ),
% 3.36/0.97      inference(superposition,[status(thm)],[c_729,c_8736]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_8745,plain,
% 3.36/0.97      ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 3.36/0.97      inference(global_propositional_subsumption,
% 3.36/0.97                [status(thm)],
% 3.36/0.97                [c_8742,c_27,c_35,c_36,c_37,c_67,c_1200,c_1825]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(c_8750,plain,
% 3.36/0.97      ( l1_struct_0(sK3) != iProver_top ),
% 3.36/0.97      inference(superposition,[status(thm)],[c_1833,c_8745]) ).
% 3.36/0.97  
% 3.36/0.97  cnf(contradiction,plain,
% 3.36/0.97      ( $false ),
% 3.36/0.97      inference(minisat,[status(thm)],[c_8750,c_1825]) ).
% 3.36/0.97  
% 3.36/0.97  
% 3.36/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.36/0.97  
% 3.36/0.97  ------                               Statistics
% 3.36/0.97  
% 3.36/0.97  ------ General
% 3.36/0.97  
% 3.36/0.97  abstr_ref_over_cycles:                  0
% 3.36/0.97  abstr_ref_under_cycles:                 0
% 3.36/0.97  gc_basic_clause_elim:                   0
% 3.36/0.97  forced_gc_time:                         0
% 3.36/0.97  parsing_time:                           0.011
% 3.36/0.97  unif_index_cands_time:                  0.
% 3.36/0.97  unif_index_add_time:                    0.
% 3.36/0.97  orderings_time:                         0.
% 3.36/0.97  out_proof_time:                         0.014
% 3.36/0.97  total_time:                             0.312
% 3.36/0.97  num_of_symbols:                         53
% 3.36/0.97  num_of_terms:                           5560
% 3.36/0.97  
% 3.36/0.97  ------ Preprocessing
% 3.36/0.97  
% 3.36/0.97  num_of_splits:                          0
% 3.36/0.97  num_of_split_atoms:                     0
% 3.36/0.97  num_of_reused_defs:                     0
% 3.36/0.97  num_eq_ax_congr_red:                    28
% 3.36/0.97  num_of_sem_filtered_clauses:            1
% 3.36/0.97  num_of_subtypes:                        5
% 3.36/0.97  monotx_restored_types:                  0
% 3.36/0.97  sat_num_of_epr_types:                   0
% 3.36/0.97  sat_num_of_non_cyclic_types:            0
% 3.36/0.97  sat_guarded_non_collapsed_types:        0
% 3.36/0.97  num_pure_diseq_elim:                    0
% 3.36/0.97  simp_replaced_by:                       0
% 3.36/0.97  res_preprocessed:                       92
% 3.36/0.97  prep_upred:                             0
% 3.36/0.97  prep_unflattend:                        0
% 3.36/0.97  smt_new_axioms:                         0
% 3.36/0.97  pred_elim_cands:                        9
% 3.36/0.97  pred_elim:                              0
% 3.36/0.97  pred_elim_cl:                           0
% 3.36/0.97  pred_elim_cycles:                       1
% 3.36/0.97  merged_defs:                            0
% 3.36/0.97  merged_defs_ncl:                        0
% 3.36/0.97  bin_hyper_res:                          0
% 3.36/0.97  prep_cycles:                            3
% 3.36/0.97  pred_elim_time:                         0.
% 3.36/0.97  splitting_time:                         0.
% 3.36/0.97  sem_filter_time:                        0.
% 3.36/0.97  monotx_time:                            0.
% 3.36/0.97  subtype_inf_time:                       0.
% 3.36/0.97  
% 3.36/0.97  ------ Problem properties
% 3.36/0.97  
% 3.36/0.97  clauses:                                25
% 3.36/0.97  conjectures:                            15
% 3.36/0.97  epr:                                    15
% 3.36/0.97  horn:                                   21
% 3.36/0.97  ground:                                 15
% 3.36/0.97  unary:                                  15
% 3.36/0.97  binary:                                 2
% 3.36/0.97  lits:                                   98
% 3.36/0.97  lits_eq:                                2
% 3.36/0.97  fd_pure:                                0
% 3.36/0.97  fd_pseudo:                              0
% 3.36/0.97  fd_cond:                                0
% 3.36/0.97  fd_pseudo_cond:                         0
% 3.36/0.97  ac_symbols:                             0
% 3.36/0.97  
% 3.36/0.97  ------ Propositional Solver
% 3.36/0.97  
% 3.36/0.97  prop_solver_calls:                      26
% 3.36/0.97  prop_fast_solver_calls:                 1415
% 3.36/0.97  smt_solver_calls:                       0
% 3.36/0.97  smt_fast_solver_calls:                  0
% 3.36/0.97  prop_num_of_clauses:                    2007
% 3.36/0.97  prop_preprocess_simplified:             6275
% 3.36/0.97  prop_fo_subsumed:                       202
% 3.36/0.97  prop_solver_time:                       0.
% 3.36/0.97  smt_solver_time:                        0.
% 3.36/0.97  smt_fast_solver_time:                   0.
% 3.36/0.97  prop_fast_solver_time:                  0.
% 3.36/0.97  prop_unsat_core_time:                   0.
% 3.36/0.97  
% 3.36/0.97  ------ QBF
% 3.36/0.97  
% 3.36/0.97  qbf_q_res:                              0
% 3.36/0.97  qbf_num_tautologies:                    0
% 3.36/0.97  qbf_prep_cycles:                        0
% 3.36/0.97  
% 3.36/0.97  ------ BMC1
% 3.36/0.97  
% 3.36/0.97  bmc1_current_bound:                     -1
% 3.36/0.97  bmc1_last_solved_bound:                 -1
% 3.36/0.97  bmc1_unsat_core_size:                   -1
% 3.36/0.97  bmc1_unsat_core_parents_size:           -1
% 3.36/0.97  bmc1_merge_next_fun:                    0
% 3.36/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.36/0.97  
% 3.36/0.97  ------ Instantiation
% 3.36/0.97  
% 3.36/0.97  inst_num_of_clauses:                    837
% 3.36/0.97  inst_num_in_passive:                    144
% 3.36/0.97  inst_num_in_active:                     432
% 3.36/0.97  inst_num_in_unprocessed:                262
% 3.36/0.97  inst_num_of_loops:                      500
% 3.36/0.97  inst_num_of_learning_restarts:          0
% 3.36/0.97  inst_num_moves_active_passive:          62
% 3.36/0.97  inst_lit_activity:                      0
% 3.36/0.97  inst_lit_activity_moves:                0
% 3.36/0.97  inst_num_tautologies:                   0
% 3.36/0.97  inst_num_prop_implied:                  0
% 3.36/0.97  inst_num_existing_simplified:           0
% 3.36/0.97  inst_num_eq_res_simplified:             0
% 3.36/0.97  inst_num_child_elim:                    0
% 3.36/0.97  inst_num_of_dismatching_blockings:      746
% 3.36/0.97  inst_num_of_non_proper_insts:           1383
% 3.36/0.97  inst_num_of_duplicates:                 0
% 3.36/0.97  inst_inst_num_from_inst_to_res:         0
% 3.36/0.97  inst_dismatching_checking_time:         0.
% 3.36/0.97  
% 3.36/0.97  ------ Resolution
% 3.36/0.97  
% 3.36/0.97  res_num_of_clauses:                     0
% 3.36/0.97  res_num_in_passive:                     0
% 3.36/0.97  res_num_in_active:                      0
% 3.36/0.97  res_num_of_loops:                       95
% 3.36/0.97  res_forward_subset_subsumed:            207
% 3.36/0.97  res_backward_subset_subsumed:           2
% 3.36/0.97  res_forward_subsumed:                   0
% 3.36/0.97  res_backward_subsumed:                  0
% 3.36/0.97  res_forward_subsumption_resolution:     0
% 3.36/0.97  res_backward_subsumption_resolution:    0
% 3.36/0.97  res_clause_to_clause_subsumption:       365
% 3.36/0.97  res_orphan_elimination:                 0
% 3.36/0.97  res_tautology_del:                      397
% 3.36/0.97  res_num_eq_res_simplified:              0
% 3.36/0.97  res_num_sel_changes:                    0
% 3.36/0.97  res_moves_from_active_to_pass:          0
% 3.36/0.97  
% 3.36/0.97  ------ Superposition
% 3.36/0.97  
% 3.36/0.97  sup_time_total:                         0.
% 3.36/0.97  sup_time_generating:                    0.
% 3.36/0.97  sup_time_sim_full:                      0.
% 3.36/0.97  sup_time_sim_immed:                     0.
% 3.36/0.97  
% 3.36/0.97  sup_num_of_clauses:                     108
% 3.36/0.97  sup_num_in_active:                      94
% 3.36/0.97  sup_num_in_passive:                     14
% 3.36/0.97  sup_num_of_loops:                       99
% 3.36/0.97  sup_fw_superposition:                   66
% 3.36/0.97  sup_bw_superposition:                   22
% 3.36/0.97  sup_immediate_simplified:               13
% 3.36/0.97  sup_given_eliminated:                   0
% 3.36/0.97  comparisons_done:                       0
% 3.36/0.97  comparisons_avoided:                    0
% 3.36/0.97  
% 3.36/0.97  ------ Simplifications
% 3.36/0.97  
% 3.36/0.97  
% 3.36/0.97  sim_fw_subset_subsumed:                 0
% 3.36/0.97  sim_bw_subset_subsumed:                 1
% 3.36/0.97  sim_fw_subsumed:                        1
% 3.36/0.97  sim_bw_subsumed:                        0
% 3.36/0.97  sim_fw_subsumption_res:                 5
% 3.36/0.97  sim_bw_subsumption_res:                 0
% 3.36/0.97  sim_tautology_del:                      1
% 3.36/0.97  sim_eq_tautology_del:                   0
% 3.36/0.97  sim_eq_res_simp:                        0
% 3.36/0.97  sim_fw_demodulated:                     1
% 3.36/0.97  sim_bw_demodulated:                     5
% 3.36/0.97  sim_light_normalised:                   15
% 3.36/0.97  sim_joinable_taut:                      0
% 3.36/0.97  sim_joinable_simp:                      0
% 3.36/0.97  sim_ac_normalised:                      0
% 3.36/0.97  sim_smt_subsumption:                    0
% 3.36/0.97  
%------------------------------------------------------------------------------
