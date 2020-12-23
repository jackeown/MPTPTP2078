%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:00 EST 2020

% Result     : Theorem 19.77s
% Output     : CNFRefutation 19.77s
% Verified   : 
% Statistics : Number of formulae       :  241 (11457 expanded)
%              Number of clauses        :  176 (2472 expanded)
%              Number of leaves         :   16 (5044 expanded)
%              Depth                    :   29
%              Number of atoms          : 1519 (169424 expanded)
%              Number of equality atoms :  630 (4433 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal clause size      :   36 (   5 average)
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
                     => ( ( m1_pre_topc(X4,X3)
                          & m1_pre_topc(X3,X2) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                       => ( ( m1_pre_topc(X4,X3)
                            & m1_pre_topc(X3,X2) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X3)
                      & m1_pre_topc(X3,X2)
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

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X3)
                      & m1_pre_topc(X3,X2)
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
    inference(flattening,[],[f28])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,sK5)),k3_tmap_1(X0,X1,X2,X4,sK5))
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X5) )
          & m1_pre_topc(X4,X3)
          & m1_pre_topc(X3,X2)
          & m1_pre_topc(X4,X0)
          & ~ v2_struct_0(X4) )
     => ( ? [X5] :
            ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,sK4,X5))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_pre_topc(sK4,X3)
        & m1_pre_topc(X3,X2)
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X5) )
              & m1_pre_topc(X4,X3)
              & m1_pre_topc(X3,X2)
              & m1_pre_topc(X4,X0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X4,k3_tmap_1(X0,X1,X2,sK3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_pre_topc(X4,sK3)
            & m1_pre_topc(sK3,X2)
            & m1_pre_topc(X4,X0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X5) )
                  & m1_pre_topc(X4,X3)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X4,X0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,sK2,X3,X5)),k3_tmap_1(X0,X1,sK2,X4,X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                    & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_pre_topc(X4,X3)
                & m1_pre_topc(X3,sK2)
                & m1_pre_topc(X4,X0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X3)
                      & m1_pre_topc(X3,X2)
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
                        ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X4,k3_tmap_1(X0,sK1,X2,X3,X5)),k3_tmap_1(X0,sK1,X2,X4,X5))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1))
                        & v1_funct_1(X5) )
                    & m1_pre_topc(X4,X3)
                    & m1_pre_topc(X3,X2)
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

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_pre_topc(X4,X3)
                        & m1_pre_topc(X3,X2)
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
                          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X4,k3_tmap_1(sK0,X1,X2,X3,X5)),k3_tmap_1(sK0,X1,X2,X4,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X3)
                      & m1_pre_topc(X3,X2)
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

fof(f36,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK3)
    & m1_pre_topc(sK3,sK2)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f29,f35,f34,f33,f32,f31,f30])).

fof(f61,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f57,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f42,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f20])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f40,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f20])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f39,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f45,plain,(
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

fof(f46,plain,(
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

fof(f59,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_307,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_812,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_306,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_813,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_306])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_312,plain,
    ( ~ m1_pre_topc(X0_48,X1_48)
    | ~ m1_pre_topc(X2_48,X0_48)
    | m1_pre_topc(X2_48,X1_48)
    | ~ l1_pre_topc(X1_48)
    | ~ v2_pre_topc(X1_48) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_807,plain,
    ( m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | m1_pre_topc(X2_48,X1_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_312])).

cnf(c_1584,plain,
    ( m1_pre_topc(X0_48,sK2) = iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_813,c_807])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_30,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_31,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_36,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_321,plain,
    ( ~ m1_pre_topc(X0_48,X1_48)
    | ~ l1_pre_topc(X1_48)
    | l1_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1089,plain,
    ( ~ m1_pre_topc(sK2,X0_48)
    | ~ l1_pre_topc(X0_48)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_1090,plain,
    ( m1_pre_topc(sK2,X0_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1089])).

cnf(c_1092,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1090])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_322,plain,
    ( ~ m1_pre_topc(X0_48,X1_48)
    | ~ l1_pre_topc(X1_48)
    | ~ v2_pre_topc(X1_48)
    | v2_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1294,plain,
    ( ~ m1_pre_topc(sK2,X0_48)
    | ~ l1_pre_topc(X0_48)
    | ~ v2_pre_topc(X0_48)
    | v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_1295,plain,
    ( m1_pre_topc(sK2,X0_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | v2_pre_topc(X0_48) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1294])).

cnf(c_1297,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1295])).

cnf(c_2492,plain,
    ( m1_pre_topc(X0_48,sK2) = iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1584,c_30,c_31,c_36,c_1092,c_1297])).

cnf(c_2498,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_812,c_2492])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_303,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_816,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_303])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_310,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_809,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_5,plain,
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
    inference(cnf_transformation,[],[f42])).

cnf(c_317,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | v1_funct_2(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),u1_struct_0(X3_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ m1_pre_topc(X3_48,X2_48)
    | ~ m1_pre_topc(X0_48,X2_48)
    | v2_struct_0(X1_48)
    | v2_struct_0(X2_48)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X2_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X2_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_802,plain,
    ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),u1_struct_0(X3_48),u1_struct_0(X1_48)) = iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X3_48,X2_48) != iProver_top
    | m1_pre_topc(X0_48,X2_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_4,plain,
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
    inference(cnf_transformation,[],[f43])).

cnf(c_318,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | m1_subset_1(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48))))
    | ~ m1_pre_topc(X3_48,X2_48)
    | ~ m1_pre_topc(X0_48,X2_48)
    | v2_struct_0(X1_48)
    | v2_struct_0(X2_48)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X2_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X2_48) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_801,plain,
    ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) = iProver_top
    | m1_pre_topc(X3_48,X2_48) != iProver_top
    | m1_pre_topc(X0_48,X2_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_319,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ m1_pre_topc(X2_48,X0_48)
    | ~ m1_pre_topc(X0_48,X3_48)
    | ~ m1_pre_topc(X2_48,X3_48)
    | v2_struct_0(X3_48)
    | v2_struct_0(X1_48)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X3_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X3_48)
    | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_800,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49)
    | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | m1_pre_topc(X0_48,X3_48) != iProver_top
    | m1_pre_topc(X2_48,X3_48) != iProver_top
    | v2_struct_0(X3_48) = iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X3_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X3_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_2189,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X4_48)) = k3_tmap_1(X5_48,X1_48,X0_48,X4_48,k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49))
    | v1_funct_2(X0_49,u1_struct_0(X3_48),u1_struct_0(X1_48)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X3_48,X2_48) != iProver_top
    | m1_pre_topc(X0_48,X2_48) != iProver_top
    | m1_pre_topc(X4_48,X0_48) != iProver_top
    | m1_pre_topc(X0_48,X5_48) != iProver_top
    | m1_pre_topc(X4_48,X5_48) != iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X5_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49)) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top
    | l1_pre_topc(X5_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top
    | v2_pre_topc(X5_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_801,c_800])).

cnf(c_4014,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X4_48)) = k3_tmap_1(X5_48,X1_48,X0_48,X4_48,k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49))
    | v1_funct_2(X0_49,u1_struct_0(X3_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X3_48,X2_48) != iProver_top
    | m1_pre_topc(X0_48,X2_48) != iProver_top
    | m1_pre_topc(X4_48,X0_48) != iProver_top
    | m1_pre_topc(X0_48,X5_48) != iProver_top
    | m1_pre_topc(X4_48,X5_48) != iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X5_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49)) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top
    | l1_pre_topc(X5_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top
    | v2_pre_topc(X5_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_802,c_2189])).

cnf(c_7311,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),u1_struct_0(X2_48)) = k3_tmap_1(X3_48,sK1,X0_48,X2_48,k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5))
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | m1_pre_topc(X0_48,X3_48) != iProver_top
    | m1_pre_topc(X2_48,X3_48) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X3_48) = iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X3_48) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X3_48) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_4014])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_32,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_33,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_34,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_43,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_44,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6,plain,
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
    inference(cnf_transformation,[],[f41])).

cnf(c_316,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ m1_pre_topc(X0_48,X2_48)
    | ~ m1_pre_topc(X3_48,X2_48)
    | v2_struct_0(X2_48)
    | v2_struct_0(X1_48)
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49))
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X2_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X2_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_803,plain,
    ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X2_48,X3_48) != iProver_top
    | m1_pre_topc(X0_48,X3_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X3_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49)) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X3_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X3_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_1820,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_803])).

cnf(c_2893,plain,
    ( v2_pre_topc(X1_48) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)) = iProver_top
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1820,c_32,c_33,c_34,c_43,c_44])).

cnf(c_2894,plain,
    ( m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v1_funct_1(k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_2893])).

cnf(c_7663,plain,
    ( v2_pre_topc(X3_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X3_48) = iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | m1_pre_topc(X2_48,X3_48) != iProver_top
    | m1_pre_topc(X0_48,X3_48) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),u1_struct_0(X2_48)) = k3_tmap_1(X3_48,sK1,X0_48,X2_48,k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5))
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X3_48) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7311,c_32,c_33,c_34,c_43,c_44,c_2894])).

cnf(c_7664,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),u1_struct_0(X2_48)) = k3_tmap_1(X3_48,sK1,X0_48,X2_48,k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5))
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | m1_pre_topc(X0_48,X3_48) != iProver_top
    | m1_pre_topc(X2_48,X3_48) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X3_48) = iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X3_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X3_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_7663])).

cnf(c_7672,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5))
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_816,c_7664])).

cnf(c_2120,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_800])).

cnf(c_3201,plain,
    ( v2_pre_topc(X1_48) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2120,c_32,c_33,c_34,c_43,c_44])).

cnf(c_3202,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_3201])).

cnf(c_3210,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK2,sK3,sK5)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_816,c_3202])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_320,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ m1_pre_topc(X2_48,X0_48)
    | v2_struct_0(X1_48)
    | v2_struct_0(X0_48)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X0_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X0_48)
    | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k2_tmap_1(X0_48,X1_48,X0_49,X2_48) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_799,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k2_tmap_1(X0_48,X1_48,X0_49,X2_48)
    | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_320])).

cnf(c_1815,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK5,X0_48)
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_799])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_35,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2771,plain,
    ( m1_pre_topc(X0_48,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK5,X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1815,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_43,c_44,c_1092,c_1297])).

cnf(c_2772,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK5,X0_48)
    | m1_pre_topc(X0_48,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2771])).

cnf(c_2777,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
    inference(superposition,[status(thm)],[c_813,c_2772])).

cnf(c_3216,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3210,c_2777])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_29,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_41,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3804,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3216,c_29,c_30,c_31,c_36,c_41])).

cnf(c_7678,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3))
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7672,c_3804])).

cnf(c_7,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_315,plain,
    ( m1_pre_topc(X0_48,X0_48)
    | ~ l1_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1228,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_1229,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1228])).

cnf(c_7670,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k3_tmap_1(sK2,sK1,sK2,sK3,sK5))
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK3,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_813,c_7664])).

cnf(c_3208,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k3_tmap_1(sK2,sK1,sK2,sK3,sK5)
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_813,c_3202])).

cnf(c_3218,plain,
    ( k3_tmap_1(sK2,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3)
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3208,c_2777])).

cnf(c_4665,plain,
    ( k3_tmap_1(sK2,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3218,c_30,c_31,c_35,c_36,c_41,c_1092,c_1229,c_1297])).

cnf(c_7680,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3))
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK3,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7670,c_4665])).

cnf(c_9937,plain,
    ( v2_pre_topc(X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | m1_pre_topc(sK3,X1_48) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3))
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7678,c_30,c_31,c_35,c_36,c_1092,c_1229,c_1297,c_7680])).

cnf(c_9938,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3))
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_9937])).

cnf(c_9949,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3))
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2498,c_9938])).

cnf(c_3808,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3804,c_801])).

cnf(c_38,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_45,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5658,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3808,c_29,c_30,c_31,c_32,c_33,c_34,c_36,c_38,c_43,c_44,c_45])).

cnf(c_5664,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X0_48)
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5658,c_799])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_37,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1240,plain,
    ( ~ m1_pre_topc(sK3,X0_48)
    | ~ l1_pre_topc(X0_48)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_1241,plain,
    ( m1_pre_topc(sK3,X0_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1240])).

cnf(c_1243,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1241])).

cnf(c_797,plain,
    ( m1_pre_topc(X0_48,X1_48) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_322])).

cnf(c_1263,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_816,c_797])).

cnf(c_3809,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3804,c_802])).

cnf(c_3810,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3804,c_2894])).

cnf(c_6182,plain,
    ( m1_pre_topc(X0_48,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5664,c_29,c_30,c_31,c_32,c_33,c_34,c_36,c_37,c_38,c_43,c_44,c_45,c_1243,c_1263,c_3809,c_3810])).

cnf(c_6183,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X0_48)
    | m1_pre_topc(X0_48,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_6182])).

cnf(c_6188,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
    inference(superposition,[status(thm)],[c_812,c_6183])).

cnf(c_9950,plain,
    ( k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9949,c_6188])).

cnf(c_42,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10203,plain,
    ( k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9950,c_30,c_31,c_35,c_36,c_41,c_42,c_1092,c_1297])).

cnf(c_301,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_818,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_301])).

cnf(c_3211,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK2,sK2,sK5)
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_818,c_3202])).

cnf(c_804,plain,
    ( m1_pre_topc(X0_48,X0_48) = iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_2778,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK5,sK2)
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_804,c_2772])).

cnf(c_1091,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1089])).

cnf(c_1296,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1294])).

cnf(c_906,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X1_48,X0_48)
    | v2_struct_0(X0_48)
    | v2_struct_0(sK1)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X0_48)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_48)
    | ~ v2_pre_topc(sK1)
    | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49,u1_struct_0(X1_48)) = k2_tmap_1(X0_48,sK1,X0_49,X1_48) ),
    inference(instantiation,[status(thm)],[c_320])).

cnf(c_1450,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X0_48,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_49,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,X0_49,X0_48) ),
    inference(instantiation,[status(thm)],[c_906])).

cnf(c_2001,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_49,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,X0_49,sK2) ),
    inference(instantiation,[status(thm)],[c_1450])).

cnf(c_2003,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK5,sK2) ),
    inference(instantiation,[status(thm)],[c_2001])).

cnf(c_3052,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK5,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2778,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_14,c_13,c_12,c_1091,c_1228,c_1296,c_2003])).

cnf(c_3215,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK2,sK5) = k2_tmap_1(sK2,sK1,sK5,sK2)
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3211,c_3052])).

cnf(c_3606,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK2,sK5) = k2_tmap_1(sK2,sK1,sK5,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3215,c_29,c_30,c_31,c_36,c_1092,c_1229])).

cnf(c_8,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_314,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,k3_tmap_1(X2_48,X1_48,X0_48,X0_48,X0_49))
    | ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ m1_pre_topc(X0_48,X2_48)
    | v2_struct_0(X1_48)
    | v2_struct_0(X0_48)
    | v2_struct_0(X2_48)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X2_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X2_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_805,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,k3_tmap_1(X2_48,X1_48,X0_48,X0_48,X0_49)) = iProver_top
    | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X0_48,X2_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_3610,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2)) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3606,c_805])).

cnf(c_4428,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3610,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_43,c_44,c_45])).

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
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_313,plain,
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
    | ~ v1_funct_1(X1_49)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X2_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X2_48) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_806,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,k2_tmap_1(X2_48,X1_48,X1_49,X0_48)) != iProver_top
    | r2_funct_2(u1_struct_0(X3_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k2_tmap_1(X2_48,X1_48,X1_49,X3_48)) = iProver_top
    | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | v1_funct_2(X1_49,u1_struct_0(X2_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X3_48,X0_48) != iProver_top
    | m1_pre_topc(X3_48,X2_48) != iProver_top
    | m1_pre_topc(X0_48,X2_48) != iProver_top
    | v2_struct_0(X3_48) = iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(X1_49) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_4432,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0_48,sK5),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4428,c_806])).

cnf(c_12836,plain,
    ( v2_struct_0(X0_48) = iProver_top
    | r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0_48,sK5),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
    | m1_pre_topc(X0_48,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4432,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_43,c_44,c_45,c_1092,c_1229,c_1297])).

cnf(c_12837,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0_48,sK5),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | v2_struct_0(X0_48) = iProver_top ),
    inference(renaming,[status(thm)],[c_12836])).

cnf(c_12843,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3)) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4665,c_12837])).

cnf(c_13378,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12843,c_37,c_41])).

cnf(c_13382,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_13378,c_806])).

cnf(c_12845,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,X1_48,X0_48,k3_tmap_1(sK2,sK1,sK2,X1_48,sK5)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK1,sK2,X1_48,sK5),u1_struct_0(X1_48),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK1,sK2,X1_48,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_48),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X1_48,sK2) != iProver_top
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK1,sK2,X1_48,sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_12837,c_806])).

cnf(c_1168,plain,
    ( ~ m1_pre_topc(X0_48,X1_48)
    | ~ m1_pre_topc(X1_48,sK2)
    | m1_pre_topc(X0_48,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_312])).

cnf(c_1169,plain,
    ( m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X1_48,sK2) != iProver_top
    | m1_pre_topc(X0_48,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1168])).

cnf(c_34695,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK1,sK2,X1_48,sK5)) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK1,sK2,X1_48,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_48),u1_struct_0(sK1)))) != iProver_top
    | r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,X1_48,X0_48,k3_tmap_1(sK2,sK1,sK2,X1_48,sK5)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK1,sK2,X1_48,sK5),u1_struct_0(X1_48),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X1_48,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12845,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_43,c_44,c_45,c_1092,c_1169,c_1297])).

cnf(c_34696,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,X1_48,X0_48,k3_tmap_1(sK2,sK1,sK2,X1_48,sK5)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK1,sK2,X1_48,sK5),u1_struct_0(X1_48),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK1,sK2,X1_48,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_48),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X1_48,sK2) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK1,sK2,X1_48,sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_34695])).

cnf(c_34702,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK1,sK2,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK1,sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK1,sK2,sK3,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4665,c_34696])).

cnf(c_34706,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_34702,c_4665])).

cnf(c_35966,plain,
    ( v2_struct_0(X0_48) = iProver_top
    | r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13382,c_29,c_30,c_31,c_32,c_33,c_34,c_36,c_37,c_38,c_41,c_43,c_44,c_45,c_3808,c_3809,c_3810,c_34706])).

cnf(c_35967,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | v2_struct_0(X0_48) = iProver_top ),
    inference(renaming,[status(thm)],[c_35966])).

cnf(c_35973,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4)) = iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_10203,c_35967])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_305,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_814,plain,
    ( m1_pre_topc(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_305])).

cnf(c_9945,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3))
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_814,c_9938])).

cnf(c_9952,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9945,c_6188])).

cnf(c_12666,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9952,c_29,c_30,c_31,c_38,c_42])).

cnf(c_3209,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK2,sK4,sK5)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_814,c_3202])).

cnf(c_2779,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK2,sK1,sK5,sK4) ),
    inference(superposition,[status(thm)],[c_2498,c_2772])).

cnf(c_3217,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_tmap_1(sK2,sK1,sK5,sK4)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3209,c_2779])).

cnf(c_1615,plain,
    ( m1_pre_topc(X0_48,sK2)
    | ~ m1_pre_topc(X0_48,sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1168])).

cnf(c_1824,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1615])).

cnf(c_1825,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) = iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1824])).

cnf(c_3930,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_tmap_1(sK2,sK1,sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3217,c_29,c_30,c_31,c_36,c_41,c_42,c_1092,c_1297,c_1825])).

cnf(c_11,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_311,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_808,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_3806,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3804,c_808])).

cnf(c_3932,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3930,c_3806])).

cnf(c_12668,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12666,c_3932])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_39,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35973,c_12668,c_42,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 19.77/3.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.77/3.00  
% 19.77/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.77/3.00  
% 19.77/3.00  ------  iProver source info
% 19.77/3.00  
% 19.77/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.77/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.77/3.00  git: non_committed_changes: false
% 19.77/3.00  git: last_make_outside_of_git: false
% 19.77/3.00  
% 19.77/3.00  ------ 
% 19.77/3.00  
% 19.77/3.00  ------ Input Options
% 19.77/3.00  
% 19.77/3.00  --out_options                           all
% 19.77/3.00  --tptp_safe_out                         true
% 19.77/3.00  --problem_path                          ""
% 19.77/3.00  --include_path                          ""
% 19.77/3.00  --clausifier                            res/vclausify_rel
% 19.77/3.00  --clausifier_options                    ""
% 19.77/3.00  --stdin                                 false
% 19.77/3.00  --stats_out                             all
% 19.77/3.00  
% 19.77/3.00  ------ General Options
% 19.77/3.00  
% 19.77/3.00  --fof                                   false
% 19.77/3.00  --time_out_real                         305.
% 19.77/3.00  --time_out_virtual                      -1.
% 19.77/3.00  --symbol_type_check                     false
% 19.77/3.00  --clausify_out                          false
% 19.77/3.00  --sig_cnt_out                           false
% 19.77/3.00  --trig_cnt_out                          false
% 19.77/3.00  --trig_cnt_out_tolerance                1.
% 19.77/3.00  --trig_cnt_out_sk_spl                   false
% 19.77/3.00  --abstr_cl_out                          false
% 19.77/3.00  
% 19.77/3.00  ------ Global Options
% 19.77/3.00  
% 19.77/3.00  --schedule                              default
% 19.77/3.00  --add_important_lit                     false
% 19.77/3.00  --prop_solver_per_cl                    1000
% 19.77/3.00  --min_unsat_core                        false
% 19.77/3.00  --soft_assumptions                      false
% 19.77/3.00  --soft_lemma_size                       3
% 19.77/3.00  --prop_impl_unit_size                   0
% 19.77/3.00  --prop_impl_unit                        []
% 19.77/3.00  --share_sel_clauses                     true
% 19.77/3.00  --reset_solvers                         false
% 19.77/3.00  --bc_imp_inh                            [conj_cone]
% 19.77/3.00  --conj_cone_tolerance                   3.
% 19.77/3.00  --extra_neg_conj                        none
% 19.77/3.00  --large_theory_mode                     true
% 19.77/3.00  --prolific_symb_bound                   200
% 19.77/3.00  --lt_threshold                          2000
% 19.77/3.00  --clause_weak_htbl                      true
% 19.77/3.00  --gc_record_bc_elim                     false
% 19.77/3.00  
% 19.77/3.00  ------ Preprocessing Options
% 19.77/3.00  
% 19.77/3.00  --preprocessing_flag                    true
% 19.77/3.00  --time_out_prep_mult                    0.1
% 19.77/3.00  --splitting_mode                        input
% 19.77/3.00  --splitting_grd                         true
% 19.77/3.00  --splitting_cvd                         false
% 19.77/3.00  --splitting_cvd_svl                     false
% 19.77/3.00  --splitting_nvd                         32
% 19.77/3.00  --sub_typing                            true
% 19.77/3.00  --prep_gs_sim                           true
% 19.77/3.00  --prep_unflatten                        true
% 19.77/3.00  --prep_res_sim                          true
% 19.77/3.00  --prep_upred                            true
% 19.77/3.00  --prep_sem_filter                       exhaustive
% 19.77/3.00  --prep_sem_filter_out                   false
% 19.77/3.00  --pred_elim                             true
% 19.77/3.00  --res_sim_input                         true
% 19.77/3.00  --eq_ax_congr_red                       true
% 19.77/3.00  --pure_diseq_elim                       true
% 19.77/3.00  --brand_transform                       false
% 19.77/3.00  --non_eq_to_eq                          false
% 19.77/3.00  --prep_def_merge                        true
% 19.77/3.00  --prep_def_merge_prop_impl              false
% 19.77/3.00  --prep_def_merge_mbd                    true
% 19.77/3.00  --prep_def_merge_tr_red                 false
% 19.77/3.00  --prep_def_merge_tr_cl                  false
% 19.77/3.00  --smt_preprocessing                     true
% 19.77/3.00  --smt_ac_axioms                         fast
% 19.77/3.00  --preprocessed_out                      false
% 19.77/3.00  --preprocessed_stats                    false
% 19.77/3.00  
% 19.77/3.00  ------ Abstraction refinement Options
% 19.77/3.00  
% 19.77/3.00  --abstr_ref                             []
% 19.77/3.00  --abstr_ref_prep                        false
% 19.77/3.00  --abstr_ref_until_sat                   false
% 19.77/3.00  --abstr_ref_sig_restrict                funpre
% 19.77/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.77/3.00  --abstr_ref_under                       []
% 19.77/3.00  
% 19.77/3.00  ------ SAT Options
% 19.77/3.00  
% 19.77/3.00  --sat_mode                              false
% 19.77/3.00  --sat_fm_restart_options                ""
% 19.77/3.00  --sat_gr_def                            false
% 19.77/3.00  --sat_epr_types                         true
% 19.77/3.00  --sat_non_cyclic_types                  false
% 19.77/3.00  --sat_finite_models                     false
% 19.77/3.00  --sat_fm_lemmas                         false
% 19.77/3.00  --sat_fm_prep                           false
% 19.77/3.00  --sat_fm_uc_incr                        true
% 19.77/3.00  --sat_out_model                         small
% 19.77/3.00  --sat_out_clauses                       false
% 19.77/3.00  
% 19.77/3.00  ------ QBF Options
% 19.77/3.00  
% 19.77/3.00  --qbf_mode                              false
% 19.77/3.00  --qbf_elim_univ                         false
% 19.77/3.00  --qbf_dom_inst                          none
% 19.77/3.00  --qbf_dom_pre_inst                      false
% 19.77/3.00  --qbf_sk_in                             false
% 19.77/3.00  --qbf_pred_elim                         true
% 19.77/3.00  --qbf_split                             512
% 19.77/3.00  
% 19.77/3.00  ------ BMC1 Options
% 19.77/3.00  
% 19.77/3.00  --bmc1_incremental                      false
% 19.77/3.00  --bmc1_axioms                           reachable_all
% 19.77/3.00  --bmc1_min_bound                        0
% 19.77/3.00  --bmc1_max_bound                        -1
% 19.77/3.00  --bmc1_max_bound_default                -1
% 19.77/3.00  --bmc1_symbol_reachability              true
% 19.77/3.00  --bmc1_property_lemmas                  false
% 19.77/3.00  --bmc1_k_induction                      false
% 19.77/3.00  --bmc1_non_equiv_states                 false
% 19.77/3.00  --bmc1_deadlock                         false
% 19.77/3.00  --bmc1_ucm                              false
% 19.77/3.00  --bmc1_add_unsat_core                   none
% 19.77/3.00  --bmc1_unsat_core_children              false
% 19.77/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.77/3.00  --bmc1_out_stat                         full
% 19.77/3.00  --bmc1_ground_init                      false
% 19.77/3.00  --bmc1_pre_inst_next_state              false
% 19.77/3.00  --bmc1_pre_inst_state                   false
% 19.77/3.00  --bmc1_pre_inst_reach_state             false
% 19.77/3.00  --bmc1_out_unsat_core                   false
% 19.77/3.00  --bmc1_aig_witness_out                  false
% 19.77/3.00  --bmc1_verbose                          false
% 19.77/3.00  --bmc1_dump_clauses_tptp                false
% 19.77/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.77/3.00  --bmc1_dump_file                        -
% 19.77/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.77/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.77/3.00  --bmc1_ucm_extend_mode                  1
% 19.77/3.00  --bmc1_ucm_init_mode                    2
% 19.77/3.00  --bmc1_ucm_cone_mode                    none
% 19.77/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.77/3.00  --bmc1_ucm_relax_model                  4
% 19.77/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.77/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.77/3.00  --bmc1_ucm_layered_model                none
% 19.77/3.00  --bmc1_ucm_max_lemma_size               10
% 19.77/3.00  
% 19.77/3.00  ------ AIG Options
% 19.77/3.00  
% 19.77/3.00  --aig_mode                              false
% 19.77/3.00  
% 19.77/3.00  ------ Instantiation Options
% 19.77/3.00  
% 19.77/3.00  --instantiation_flag                    true
% 19.77/3.00  --inst_sos_flag                         true
% 19.77/3.00  --inst_sos_phase                        true
% 19.77/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.77/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.77/3.00  --inst_lit_sel_side                     num_symb
% 19.77/3.00  --inst_solver_per_active                1400
% 19.77/3.00  --inst_solver_calls_frac                1.
% 19.77/3.00  --inst_passive_queue_type               priority_queues
% 19.77/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.77/3.00  --inst_passive_queues_freq              [25;2]
% 19.77/3.00  --inst_dismatching                      true
% 19.77/3.00  --inst_eager_unprocessed_to_passive     true
% 19.77/3.00  --inst_prop_sim_given                   true
% 19.77/3.00  --inst_prop_sim_new                     false
% 19.77/3.00  --inst_subs_new                         false
% 19.77/3.00  --inst_eq_res_simp                      false
% 19.77/3.00  --inst_subs_given                       false
% 19.77/3.00  --inst_orphan_elimination               true
% 19.77/3.00  --inst_learning_loop_flag               true
% 19.77/3.00  --inst_learning_start                   3000
% 19.77/3.00  --inst_learning_factor                  2
% 19.77/3.00  --inst_start_prop_sim_after_learn       3
% 19.77/3.00  --inst_sel_renew                        solver
% 19.77/3.00  --inst_lit_activity_flag                true
% 19.77/3.00  --inst_restr_to_given                   false
% 19.77/3.00  --inst_activity_threshold               500
% 19.77/3.00  --inst_out_proof                        true
% 19.77/3.00  
% 19.77/3.00  ------ Resolution Options
% 19.77/3.00  
% 19.77/3.00  --resolution_flag                       true
% 19.77/3.00  --res_lit_sel                           adaptive
% 19.77/3.00  --res_lit_sel_side                      none
% 19.77/3.00  --res_ordering                          kbo
% 19.77/3.00  --res_to_prop_solver                    active
% 19.77/3.00  --res_prop_simpl_new                    false
% 19.77/3.00  --res_prop_simpl_given                  true
% 19.77/3.00  --res_passive_queue_type                priority_queues
% 19.77/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.77/3.00  --res_passive_queues_freq               [15;5]
% 19.77/3.00  --res_forward_subs                      full
% 19.77/3.00  --res_backward_subs                     full
% 19.77/3.00  --res_forward_subs_resolution           true
% 19.77/3.00  --res_backward_subs_resolution          true
% 19.77/3.00  --res_orphan_elimination                true
% 19.77/3.00  --res_time_limit                        2.
% 19.77/3.00  --res_out_proof                         true
% 19.77/3.00  
% 19.77/3.00  ------ Superposition Options
% 19.77/3.00  
% 19.77/3.00  --superposition_flag                    true
% 19.77/3.00  --sup_passive_queue_type                priority_queues
% 19.77/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.77/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.77/3.00  --demod_completeness_check              fast
% 19.77/3.00  --demod_use_ground                      true
% 19.77/3.00  --sup_to_prop_solver                    passive
% 19.77/3.00  --sup_prop_simpl_new                    true
% 19.77/3.00  --sup_prop_simpl_given                  true
% 19.77/3.00  --sup_fun_splitting                     true
% 19.77/3.00  --sup_smt_interval                      50000
% 19.77/3.00  
% 19.77/3.00  ------ Superposition Simplification Setup
% 19.77/3.00  
% 19.77/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.77/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.77/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.77/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.77/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.77/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.77/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.77/3.00  --sup_immed_triv                        [TrivRules]
% 19.77/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.77/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.77/3.00  --sup_immed_bw_main                     []
% 19.77/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.77/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.77/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.77/3.00  --sup_input_bw                          []
% 19.77/3.00  
% 19.77/3.00  ------ Combination Options
% 19.77/3.00  
% 19.77/3.00  --comb_res_mult                         3
% 19.77/3.00  --comb_sup_mult                         2
% 19.77/3.00  --comb_inst_mult                        10
% 19.77/3.00  
% 19.77/3.00  ------ Debug Options
% 19.77/3.00  
% 19.77/3.00  --dbg_backtrace                         false
% 19.77/3.00  --dbg_dump_prop_clauses                 false
% 19.77/3.00  --dbg_dump_prop_clauses_file            -
% 19.77/3.00  --dbg_out_stat                          false
% 19.77/3.00  ------ Parsing...
% 19.77/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.77/3.00  
% 19.77/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.77/3.00  
% 19.77/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.77/3.00  
% 19.77/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.77/3.00  ------ Proving...
% 19.77/3.00  ------ Problem Properties 
% 19.77/3.00  
% 19.77/3.00  
% 19.77/3.00  clauses                                 29
% 19.77/3.00  conjectures                             18
% 19.77/3.00  EPR                                     19
% 19.77/3.00  Horn                                    22
% 19.77/3.00  unary                                   18
% 19.77/3.00  binary                                  1
% 19.77/3.00  lits                                    123
% 19.77/3.00  lits eq                                 2
% 19.77/3.00  fd_pure                                 0
% 19.77/3.00  fd_pseudo                               0
% 19.77/3.00  fd_cond                                 0
% 19.77/3.00  fd_pseudo_cond                          0
% 19.77/3.00  AC symbols                              0
% 19.77/3.00  
% 19.77/3.00  ------ Schedule dynamic 5 is on 
% 19.77/3.00  
% 19.77/3.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.77/3.00  
% 19.77/3.00  
% 19.77/3.00  ------ 
% 19.77/3.00  Current options:
% 19.77/3.00  ------ 
% 19.77/3.00  
% 19.77/3.00  ------ Input Options
% 19.77/3.00  
% 19.77/3.00  --out_options                           all
% 19.77/3.00  --tptp_safe_out                         true
% 19.77/3.00  --problem_path                          ""
% 19.77/3.00  --include_path                          ""
% 19.77/3.00  --clausifier                            res/vclausify_rel
% 19.77/3.00  --clausifier_options                    ""
% 19.77/3.00  --stdin                                 false
% 19.77/3.00  --stats_out                             all
% 19.77/3.00  
% 19.77/3.00  ------ General Options
% 19.77/3.00  
% 19.77/3.00  --fof                                   false
% 19.77/3.00  --time_out_real                         305.
% 19.77/3.00  --time_out_virtual                      -1.
% 19.77/3.00  --symbol_type_check                     false
% 19.77/3.00  --clausify_out                          false
% 19.77/3.00  --sig_cnt_out                           false
% 19.77/3.00  --trig_cnt_out                          false
% 19.77/3.00  --trig_cnt_out_tolerance                1.
% 19.77/3.00  --trig_cnt_out_sk_spl                   false
% 19.77/3.00  --abstr_cl_out                          false
% 19.77/3.00  
% 19.77/3.00  ------ Global Options
% 19.77/3.00  
% 19.77/3.00  --schedule                              default
% 19.77/3.00  --add_important_lit                     false
% 19.77/3.00  --prop_solver_per_cl                    1000
% 19.77/3.00  --min_unsat_core                        false
% 19.77/3.00  --soft_assumptions                      false
% 19.77/3.00  --soft_lemma_size                       3
% 19.77/3.00  --prop_impl_unit_size                   0
% 19.77/3.00  --prop_impl_unit                        []
% 19.77/3.00  --share_sel_clauses                     true
% 19.77/3.00  --reset_solvers                         false
% 19.77/3.00  --bc_imp_inh                            [conj_cone]
% 19.77/3.00  --conj_cone_tolerance                   3.
% 19.77/3.00  --extra_neg_conj                        none
% 19.77/3.00  --large_theory_mode                     true
% 19.77/3.00  --prolific_symb_bound                   200
% 19.77/3.00  --lt_threshold                          2000
% 19.77/3.00  --clause_weak_htbl                      true
% 19.77/3.00  --gc_record_bc_elim                     false
% 19.77/3.00  
% 19.77/3.00  ------ Preprocessing Options
% 19.77/3.00  
% 19.77/3.00  --preprocessing_flag                    true
% 19.77/3.00  --time_out_prep_mult                    0.1
% 19.77/3.00  --splitting_mode                        input
% 19.77/3.00  --splitting_grd                         true
% 19.77/3.00  --splitting_cvd                         false
% 19.77/3.00  --splitting_cvd_svl                     false
% 19.77/3.00  --splitting_nvd                         32
% 19.77/3.00  --sub_typing                            true
% 19.77/3.00  --prep_gs_sim                           true
% 19.77/3.00  --prep_unflatten                        true
% 19.77/3.00  --prep_res_sim                          true
% 19.77/3.00  --prep_upred                            true
% 19.77/3.00  --prep_sem_filter                       exhaustive
% 19.77/3.00  --prep_sem_filter_out                   false
% 19.77/3.00  --pred_elim                             true
% 19.77/3.00  --res_sim_input                         true
% 19.77/3.00  --eq_ax_congr_red                       true
% 19.77/3.00  --pure_diseq_elim                       true
% 19.77/3.00  --brand_transform                       false
% 19.77/3.00  --non_eq_to_eq                          false
% 19.77/3.00  --prep_def_merge                        true
% 19.77/3.00  --prep_def_merge_prop_impl              false
% 19.77/3.00  --prep_def_merge_mbd                    true
% 19.77/3.00  --prep_def_merge_tr_red                 false
% 19.77/3.00  --prep_def_merge_tr_cl                  false
% 19.77/3.00  --smt_preprocessing                     true
% 19.77/3.00  --smt_ac_axioms                         fast
% 19.77/3.00  --preprocessed_out                      false
% 19.77/3.00  --preprocessed_stats                    false
% 19.77/3.00  
% 19.77/3.00  ------ Abstraction refinement Options
% 19.77/3.00  
% 19.77/3.00  --abstr_ref                             []
% 19.77/3.00  --abstr_ref_prep                        false
% 19.77/3.00  --abstr_ref_until_sat                   false
% 19.77/3.00  --abstr_ref_sig_restrict                funpre
% 19.77/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.77/3.00  --abstr_ref_under                       []
% 19.77/3.00  
% 19.77/3.00  ------ SAT Options
% 19.77/3.00  
% 19.77/3.00  --sat_mode                              false
% 19.77/3.00  --sat_fm_restart_options                ""
% 19.77/3.00  --sat_gr_def                            false
% 19.77/3.00  --sat_epr_types                         true
% 19.77/3.00  --sat_non_cyclic_types                  false
% 19.77/3.00  --sat_finite_models                     false
% 19.77/3.00  --sat_fm_lemmas                         false
% 19.77/3.00  --sat_fm_prep                           false
% 19.77/3.00  --sat_fm_uc_incr                        true
% 19.77/3.00  --sat_out_model                         small
% 19.77/3.00  --sat_out_clauses                       false
% 19.77/3.00  
% 19.77/3.00  ------ QBF Options
% 19.77/3.00  
% 19.77/3.00  --qbf_mode                              false
% 19.77/3.00  --qbf_elim_univ                         false
% 19.77/3.00  --qbf_dom_inst                          none
% 19.77/3.00  --qbf_dom_pre_inst                      false
% 19.77/3.00  --qbf_sk_in                             false
% 19.77/3.00  --qbf_pred_elim                         true
% 19.77/3.00  --qbf_split                             512
% 19.77/3.00  
% 19.77/3.00  ------ BMC1 Options
% 19.77/3.00  
% 19.77/3.00  --bmc1_incremental                      false
% 19.77/3.00  --bmc1_axioms                           reachable_all
% 19.77/3.00  --bmc1_min_bound                        0
% 19.77/3.00  --bmc1_max_bound                        -1
% 19.77/3.00  --bmc1_max_bound_default                -1
% 19.77/3.00  --bmc1_symbol_reachability              true
% 19.77/3.00  --bmc1_property_lemmas                  false
% 19.77/3.00  --bmc1_k_induction                      false
% 19.77/3.00  --bmc1_non_equiv_states                 false
% 19.77/3.00  --bmc1_deadlock                         false
% 19.77/3.00  --bmc1_ucm                              false
% 19.77/3.00  --bmc1_add_unsat_core                   none
% 19.77/3.00  --bmc1_unsat_core_children              false
% 19.77/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.77/3.00  --bmc1_out_stat                         full
% 19.77/3.00  --bmc1_ground_init                      false
% 19.77/3.00  --bmc1_pre_inst_next_state              false
% 19.77/3.00  --bmc1_pre_inst_state                   false
% 19.77/3.00  --bmc1_pre_inst_reach_state             false
% 19.77/3.00  --bmc1_out_unsat_core                   false
% 19.77/3.00  --bmc1_aig_witness_out                  false
% 19.77/3.00  --bmc1_verbose                          false
% 19.77/3.00  --bmc1_dump_clauses_tptp                false
% 19.77/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.77/3.00  --bmc1_dump_file                        -
% 19.77/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.77/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.77/3.00  --bmc1_ucm_extend_mode                  1
% 19.77/3.00  --bmc1_ucm_init_mode                    2
% 19.77/3.00  --bmc1_ucm_cone_mode                    none
% 19.77/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.77/3.00  --bmc1_ucm_relax_model                  4
% 19.77/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.77/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.77/3.00  --bmc1_ucm_layered_model                none
% 19.77/3.00  --bmc1_ucm_max_lemma_size               10
% 19.77/3.00  
% 19.77/3.00  ------ AIG Options
% 19.77/3.00  
% 19.77/3.00  --aig_mode                              false
% 19.77/3.00  
% 19.77/3.00  ------ Instantiation Options
% 19.77/3.00  
% 19.77/3.00  --instantiation_flag                    true
% 19.77/3.00  --inst_sos_flag                         true
% 19.77/3.00  --inst_sos_phase                        true
% 19.77/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.77/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.77/3.00  --inst_lit_sel_side                     none
% 19.77/3.00  --inst_solver_per_active                1400
% 19.77/3.00  --inst_solver_calls_frac                1.
% 19.77/3.00  --inst_passive_queue_type               priority_queues
% 19.77/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.77/3.00  --inst_passive_queues_freq              [25;2]
% 19.77/3.00  --inst_dismatching                      true
% 19.77/3.00  --inst_eager_unprocessed_to_passive     true
% 19.77/3.00  --inst_prop_sim_given                   true
% 19.77/3.00  --inst_prop_sim_new                     false
% 19.77/3.00  --inst_subs_new                         false
% 19.77/3.00  --inst_eq_res_simp                      false
% 19.77/3.00  --inst_subs_given                       false
% 19.77/3.00  --inst_orphan_elimination               true
% 19.77/3.00  --inst_learning_loop_flag               true
% 19.77/3.00  --inst_learning_start                   3000
% 19.77/3.00  --inst_learning_factor                  2
% 19.77/3.00  --inst_start_prop_sim_after_learn       3
% 19.77/3.00  --inst_sel_renew                        solver
% 19.77/3.00  --inst_lit_activity_flag                true
% 19.77/3.00  --inst_restr_to_given                   false
% 19.77/3.00  --inst_activity_threshold               500
% 19.77/3.00  --inst_out_proof                        true
% 19.77/3.00  
% 19.77/3.00  ------ Resolution Options
% 19.77/3.00  
% 19.77/3.00  --resolution_flag                       false
% 19.77/3.00  --res_lit_sel                           adaptive
% 19.77/3.00  --res_lit_sel_side                      none
% 19.77/3.00  --res_ordering                          kbo
% 19.77/3.00  --res_to_prop_solver                    active
% 19.77/3.00  --res_prop_simpl_new                    false
% 19.77/3.00  --res_prop_simpl_given                  true
% 19.77/3.00  --res_passive_queue_type                priority_queues
% 19.77/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.77/3.00  --res_passive_queues_freq               [15;5]
% 19.77/3.00  --res_forward_subs                      full
% 19.77/3.00  --res_backward_subs                     full
% 19.77/3.00  --res_forward_subs_resolution           true
% 19.77/3.00  --res_backward_subs_resolution          true
% 19.77/3.00  --res_orphan_elimination                true
% 19.77/3.00  --res_time_limit                        2.
% 19.77/3.00  --res_out_proof                         true
% 19.77/3.00  
% 19.77/3.00  ------ Superposition Options
% 19.77/3.00  
% 19.77/3.00  --superposition_flag                    true
% 19.77/3.00  --sup_passive_queue_type                priority_queues
% 19.77/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.77/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.77/3.00  --demod_completeness_check              fast
% 19.77/3.00  --demod_use_ground                      true
% 19.77/3.00  --sup_to_prop_solver                    passive
% 19.77/3.00  --sup_prop_simpl_new                    true
% 19.77/3.00  --sup_prop_simpl_given                  true
% 19.77/3.00  --sup_fun_splitting                     true
% 19.77/3.00  --sup_smt_interval                      50000
% 19.77/3.00  
% 19.77/3.00  ------ Superposition Simplification Setup
% 19.77/3.00  
% 19.77/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.77/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.77/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.77/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.77/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.77/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.77/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.77/3.00  --sup_immed_triv                        [TrivRules]
% 19.77/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.77/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.77/3.00  --sup_immed_bw_main                     []
% 19.77/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.77/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.77/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.77/3.00  --sup_input_bw                          []
% 19.77/3.00  
% 19.77/3.00  ------ Combination Options
% 19.77/3.00  
% 19.77/3.00  --comb_res_mult                         3
% 19.77/3.00  --comb_sup_mult                         2
% 19.77/3.00  --comb_inst_mult                        10
% 19.77/3.00  
% 19.77/3.00  ------ Debug Options
% 19.77/3.00  
% 19.77/3.00  --dbg_backtrace                         false
% 19.77/3.00  --dbg_dump_prop_clauses                 false
% 19.77/3.00  --dbg_dump_prop_clauses_file            -
% 19.77/3.00  --dbg_out_stat                          false
% 19.77/3.00  
% 19.77/3.00  
% 19.77/3.00  
% 19.77/3.00  
% 19.77/3.00  ------ Proving...
% 19.77/3.00  
% 19.77/3.00  
% 19.77/3.00  % SZS status Theorem for theBenchmark.p
% 19.77/3.00  
% 19.77/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.77/3.00  
% 19.77/3.00  fof(f10,conjecture,(
% 19.77/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 19.77/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.77/3.00  
% 19.77/3.00  fof(f11,negated_conjecture,(
% 19.77/3.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 19.77/3.00    inference(negated_conjecture,[],[f10])).
% 19.77/3.00  
% 19.77/3.00  fof(f28,plain,(
% 19.77/3.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2))) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 19.77/3.00    inference(ennf_transformation,[],[f11])).
% 19.77/3.00  
% 19.77/3.00  fof(f29,plain,(
% 19.77/3.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 19.77/3.00    inference(flattening,[],[f28])).
% 19.77/3.00  
% 19.77/3.00  fof(f35,plain,(
% 19.77/3.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,sK5)),k3_tmap_1(X0,X1,X2,X4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 19.77/3.00    introduced(choice_axiom,[])).
% 19.77/3.00  
% 19.77/3.00  fof(f34,plain,(
% 19.77/3.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (? [X5] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,sK4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(sK4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 19.77/3.00    introduced(choice_axiom,[])).
% 19.77/3.00  
% 19.77/3.00  fof(f33,plain,(
% 19.77/3.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X4,k3_tmap_1(X0,X1,X2,sK3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK3) & m1_pre_topc(sK3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 19.77/3.00    introduced(choice_axiom,[])).
% 19.77/3.00  
% 19.77/3.00  fof(f32,plain,(
% 19.77/3.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,sK2,X3,X5)),k3_tmap_1(X0,X1,sK2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,sK2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 19.77/3.00    introduced(choice_axiom,[])).
% 19.77/3.00  
% 19.77/3.00  fof(f31,plain,(
% 19.77/3.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X4,k3_tmap_1(X0,sK1,X2,X3,X5)),k3_tmap_1(X0,sK1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 19.77/3.00    introduced(choice_axiom,[])).
% 19.77/3.00  
% 19.77/3.00  fof(f30,plain,(
% 19.77/3.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X4,k3_tmap_1(sK0,X1,X2,X3,X5)),k3_tmap_1(sK0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 19.77/3.00    introduced(choice_axiom,[])).
% 19.77/3.00  
% 19.77/3.00  fof(f36,plain,(
% 19.77/3.00    (((((~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK3) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 19.77/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f29,f35,f34,f33,f32,f31,f30])).
% 19.77/3.00  
% 19.77/3.00  fof(f61,plain,(
% 19.77/3.00    m1_pre_topc(sK4,sK3)),
% 19.77/3.00    inference(cnf_transformation,[],[f36])).
% 19.77/3.00  
% 19.77/3.00  fof(f60,plain,(
% 19.77/3.00    m1_pre_topc(sK3,sK2)),
% 19.77/3.00    inference(cnf_transformation,[],[f36])).
% 19.77/3.00  
% 19.77/3.00  fof(f9,axiom,(
% 19.77/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 19.77/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.77/3.00  
% 19.77/3.00  fof(f26,plain,(
% 19.77/3.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 19.77/3.00    inference(ennf_transformation,[],[f9])).
% 19.77/3.00  
% 19.77/3.00  fof(f27,plain,(
% 19.77/3.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.77/3.00    inference(flattening,[],[f26])).
% 19.77/3.00  
% 19.77/3.00  fof(f47,plain,(
% 19.77/3.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 19.77/3.00    inference(cnf_transformation,[],[f27])).
% 19.77/3.00  
% 19.77/3.00  fof(f49,plain,(
% 19.77/3.00    v2_pre_topc(sK0)),
% 19.77/3.00    inference(cnf_transformation,[],[f36])).
% 19.77/3.00  
% 19.77/3.00  fof(f50,plain,(
% 19.77/3.00    l1_pre_topc(sK0)),
% 19.77/3.00    inference(cnf_transformation,[],[f36])).
% 19.77/3.00  
% 19.77/3.00  fof(f55,plain,(
% 19.77/3.00    m1_pre_topc(sK2,sK0)),
% 19.77/3.00    inference(cnf_transformation,[],[f36])).
% 19.77/3.00  
% 19.77/3.00  fof(f2,axiom,(
% 19.77/3.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 19.77/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.77/3.00  
% 19.77/3.00  fof(f14,plain,(
% 19.77/3.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 19.77/3.00    inference(ennf_transformation,[],[f2])).
% 19.77/3.00  
% 19.77/3.00  fof(f38,plain,(
% 19.77/3.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 19.77/3.00    inference(cnf_transformation,[],[f14])).
% 19.77/3.00  
% 19.77/3.00  fof(f1,axiom,(
% 19.77/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 19.77/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.77/3.00  
% 19.77/3.00  fof(f12,plain,(
% 19.77/3.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 19.77/3.00    inference(ennf_transformation,[],[f1])).
% 19.77/3.00  
% 19.77/3.00  fof(f13,plain,(
% 19.77/3.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.77/3.00    inference(flattening,[],[f12])).
% 19.77/3.00  
% 19.77/3.00  fof(f37,plain,(
% 19.77/3.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 19.77/3.00    inference(cnf_transformation,[],[f13])).
% 19.77/3.00  
% 19.77/3.00  fof(f57,plain,(
% 19.77/3.00    m1_pre_topc(sK3,sK0)),
% 19.77/3.00    inference(cnf_transformation,[],[f36])).
% 19.77/3.00  
% 19.77/3.00  fof(f64,plain,(
% 19.77/3.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 19.77/3.00    inference(cnf_transformation,[],[f36])).
% 19.77/3.00  
% 19.77/3.00  fof(f5,axiom,(
% 19.77/3.00    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 19.77/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.77/3.00  
% 19.77/3.00  fof(f19,plain,(
% 19.77/3.00    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.77/3.00    inference(ennf_transformation,[],[f5])).
% 19.77/3.00  
% 19.77/3.00  fof(f20,plain,(
% 19.77/3.00    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.77/3.00    inference(flattening,[],[f19])).
% 19.77/3.00  
% 19.77/3.00  fof(f42,plain,(
% 19.77/3.00    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.77/3.00    inference(cnf_transformation,[],[f20])).
% 19.77/3.00  
% 19.77/3.00  fof(f43,plain,(
% 19.77/3.00    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.77/3.00    inference(cnf_transformation,[],[f20])).
% 19.77/3.00  
% 19.77/3.00  fof(f4,axiom,(
% 19.77/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 19.77/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.77/3.00  
% 19.77/3.00  fof(f17,plain,(
% 19.77/3.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.77/3.00    inference(ennf_transformation,[],[f4])).
% 19.77/3.00  
% 19.77/3.00  fof(f18,plain,(
% 19.77/3.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.77/3.00    inference(flattening,[],[f17])).
% 19.77/3.00  
% 19.77/3.00  fof(f40,plain,(
% 19.77/3.00    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.77/3.00    inference(cnf_transformation,[],[f18])).
% 19.77/3.00  
% 19.77/3.00  fof(f51,plain,(
% 19.77/3.00    ~v2_struct_0(sK1)),
% 19.77/3.00    inference(cnf_transformation,[],[f36])).
% 19.77/3.00  
% 19.77/3.00  fof(f52,plain,(
% 19.77/3.00    v2_pre_topc(sK1)),
% 19.77/3.00    inference(cnf_transformation,[],[f36])).
% 19.77/3.00  
% 19.77/3.00  fof(f53,plain,(
% 19.77/3.00    l1_pre_topc(sK1)),
% 19.77/3.00    inference(cnf_transformation,[],[f36])).
% 19.77/3.00  
% 19.77/3.00  fof(f62,plain,(
% 19.77/3.00    v1_funct_1(sK5)),
% 19.77/3.00    inference(cnf_transformation,[],[f36])).
% 19.77/3.00  
% 19.77/3.00  fof(f63,plain,(
% 19.77/3.00    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))),
% 19.77/3.00    inference(cnf_transformation,[],[f36])).
% 19.77/3.00  
% 19.77/3.00  fof(f41,plain,(
% 19.77/3.00    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.77/3.00    inference(cnf_transformation,[],[f20])).
% 19.77/3.00  
% 19.77/3.00  fof(f3,axiom,(
% 19.77/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 19.77/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.77/3.00  
% 19.77/3.00  fof(f15,plain,(
% 19.77/3.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.77/3.00    inference(ennf_transformation,[],[f3])).
% 19.77/3.00  
% 19.77/3.00  fof(f16,plain,(
% 19.77/3.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.77/3.00    inference(flattening,[],[f15])).
% 19.77/3.00  
% 19.77/3.00  fof(f39,plain,(
% 19.77/3.00    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.77/3.00    inference(cnf_transformation,[],[f16])).
% 19.77/3.00  
% 19.77/3.00  fof(f54,plain,(
% 19.77/3.00    ~v2_struct_0(sK2)),
% 19.77/3.00    inference(cnf_transformation,[],[f36])).
% 19.77/3.00  
% 19.77/3.00  fof(f48,plain,(
% 19.77/3.00    ~v2_struct_0(sK0)),
% 19.77/3.00    inference(cnf_transformation,[],[f36])).
% 19.77/3.00  
% 19.77/3.00  fof(f6,axiom,(
% 19.77/3.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 19.77/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.77/3.00  
% 19.77/3.00  fof(f21,plain,(
% 19.77/3.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 19.77/3.00    inference(ennf_transformation,[],[f6])).
% 19.77/3.00  
% 19.77/3.00  fof(f44,plain,(
% 19.77/3.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 19.77/3.00    inference(cnf_transformation,[],[f21])).
% 19.77/3.00  
% 19.77/3.00  fof(f56,plain,(
% 19.77/3.00    ~v2_struct_0(sK3)),
% 19.77/3.00    inference(cnf_transformation,[],[f36])).
% 19.77/3.00  
% 19.77/3.00  fof(f7,axiom,(
% 19.77/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 19.77/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.77/3.00  
% 19.77/3.00  fof(f22,plain,(
% 19.77/3.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.77/3.00    inference(ennf_transformation,[],[f7])).
% 19.77/3.00  
% 19.77/3.00  fof(f23,plain,(
% 19.77/3.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.77/3.00    inference(flattening,[],[f22])).
% 19.77/3.00  
% 19.77/3.00  fof(f45,plain,(
% 19.77/3.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.77/3.00    inference(cnf_transformation,[],[f23])).
% 19.77/3.00  
% 19.77/3.00  fof(f8,axiom,(
% 19.77/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_pre_topc(X3,X2) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))) => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 19.77/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.77/3.00  
% 19.77/3.00  fof(f24,plain,(
% 19.77/3.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | (~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.77/3.00    inference(ennf_transformation,[],[f8])).
% 19.77/3.00  
% 19.77/3.00  fof(f25,plain,(
% 19.77/3.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.77/3.00    inference(flattening,[],[f24])).
% 19.77/3.00  
% 19.77/3.00  fof(f46,plain,(
% 19.77/3.00    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.77/3.00    inference(cnf_transformation,[],[f25])).
% 19.77/3.00  
% 19.77/3.00  fof(f59,plain,(
% 19.77/3.00    m1_pre_topc(sK4,sK0)),
% 19.77/3.00    inference(cnf_transformation,[],[f36])).
% 19.77/3.00  
% 19.77/3.00  fof(f65,plain,(
% 19.77/3.00    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5))),
% 19.77/3.00    inference(cnf_transformation,[],[f36])).
% 19.77/3.00  
% 19.77/3.00  fof(f58,plain,(
% 19.77/3.00    ~v2_struct_0(sK4)),
% 19.77/3.00    inference(cnf_transformation,[],[f36])).
% 19.77/3.00  
% 19.77/3.00  cnf(c_15,negated_conjecture,
% 19.77/3.00      ( m1_pre_topc(sK4,sK3) ),
% 19.77/3.00      inference(cnf_transformation,[],[f61]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_307,negated_conjecture,
% 19.77/3.00      ( m1_pre_topc(sK4,sK3) ),
% 19.77/3.00      inference(subtyping,[status(esa)],[c_15]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_812,plain,
% 19.77/3.00      ( m1_pre_topc(sK4,sK3) = iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_16,negated_conjecture,
% 19.77/3.00      ( m1_pre_topc(sK3,sK2) ),
% 19.77/3.00      inference(cnf_transformation,[],[f60]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_306,negated_conjecture,
% 19.77/3.00      ( m1_pre_topc(sK3,sK2) ),
% 19.77/3.00      inference(subtyping,[status(esa)],[c_16]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_813,plain,
% 19.77/3.00      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_306]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_10,plain,
% 19.77/3.00      ( ~ m1_pre_topc(X0,X1)
% 19.77/3.00      | ~ m1_pre_topc(X2,X0)
% 19.77/3.00      | m1_pre_topc(X2,X1)
% 19.77/3.00      | ~ l1_pre_topc(X1)
% 19.77/3.00      | ~ v2_pre_topc(X1) ),
% 19.77/3.00      inference(cnf_transformation,[],[f47]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_312,plain,
% 19.77/3.00      ( ~ m1_pre_topc(X0_48,X1_48)
% 19.77/3.00      | ~ m1_pre_topc(X2_48,X0_48)
% 19.77/3.00      | m1_pre_topc(X2_48,X1_48)
% 19.77/3.00      | ~ l1_pre_topc(X1_48)
% 19.77/3.00      | ~ v2_pre_topc(X1_48) ),
% 19.77/3.00      inference(subtyping,[status(esa)],[c_10]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_807,plain,
% 19.77/3.00      ( m1_pre_topc(X0_48,X1_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X2_48,X1_48) = iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_312]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_1584,plain,
% 19.77/3.00      ( m1_pre_topc(X0_48,sK2) = iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,sK3) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK2) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK2) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_813,c_807]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_27,negated_conjecture,
% 19.77/3.00      ( v2_pre_topc(sK0) ),
% 19.77/3.00      inference(cnf_transformation,[],[f49]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_30,plain,
% 19.77/3.00      ( v2_pre_topc(sK0) = iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_26,negated_conjecture,
% 19.77/3.00      ( l1_pre_topc(sK0) ),
% 19.77/3.00      inference(cnf_transformation,[],[f50]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_31,plain,
% 19.77/3.00      ( l1_pre_topc(sK0) = iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_21,negated_conjecture,
% 19.77/3.00      ( m1_pre_topc(sK2,sK0) ),
% 19.77/3.00      inference(cnf_transformation,[],[f55]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_36,plain,
% 19.77/3.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_1,plain,
% 19.77/3.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 19.77/3.00      inference(cnf_transformation,[],[f38]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_321,plain,
% 19.77/3.00      ( ~ m1_pre_topc(X0_48,X1_48)
% 19.77/3.00      | ~ l1_pre_topc(X1_48)
% 19.77/3.00      | l1_pre_topc(X0_48) ),
% 19.77/3.00      inference(subtyping,[status(esa)],[c_1]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_1089,plain,
% 19.77/3.00      ( ~ m1_pre_topc(sK2,X0_48)
% 19.77/3.00      | ~ l1_pre_topc(X0_48)
% 19.77/3.00      | l1_pre_topc(sK2) ),
% 19.77/3.00      inference(instantiation,[status(thm)],[c_321]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_1090,plain,
% 19.77/3.00      ( m1_pre_topc(sK2,X0_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(X0_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK2) = iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_1089]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_1092,plain,
% 19.77/3.00      ( m1_pre_topc(sK2,sK0) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK2) = iProver_top
% 19.77/3.00      | l1_pre_topc(sK0) != iProver_top ),
% 19.77/3.00      inference(instantiation,[status(thm)],[c_1090]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_0,plain,
% 19.77/3.00      ( ~ m1_pre_topc(X0,X1)
% 19.77/3.00      | ~ l1_pre_topc(X1)
% 19.77/3.00      | ~ v2_pre_topc(X1)
% 19.77/3.00      | v2_pre_topc(X0) ),
% 19.77/3.00      inference(cnf_transformation,[],[f37]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_322,plain,
% 19.77/3.00      ( ~ m1_pre_topc(X0_48,X1_48)
% 19.77/3.00      | ~ l1_pre_topc(X1_48)
% 19.77/3.00      | ~ v2_pre_topc(X1_48)
% 19.77/3.00      | v2_pre_topc(X0_48) ),
% 19.77/3.00      inference(subtyping,[status(esa)],[c_0]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_1294,plain,
% 19.77/3.00      ( ~ m1_pre_topc(sK2,X0_48)
% 19.77/3.00      | ~ l1_pre_topc(X0_48)
% 19.77/3.00      | ~ v2_pre_topc(X0_48)
% 19.77/3.00      | v2_pre_topc(sK2) ),
% 19.77/3.00      inference(instantiation,[status(thm)],[c_322]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_1295,plain,
% 19.77/3.00      ( m1_pre_topc(sK2,X0_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(X0_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X0_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK2) = iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_1294]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_1297,plain,
% 19.77/3.00      ( m1_pre_topc(sK2,sK0) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK0) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK2) = iProver_top
% 19.77/3.00      | v2_pre_topc(sK0) != iProver_top ),
% 19.77/3.00      inference(instantiation,[status(thm)],[c_1295]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_2492,plain,
% 19.77/3.00      ( m1_pre_topc(X0_48,sK2) = iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,sK3) != iProver_top ),
% 19.77/3.00      inference(global_propositional_subsumption,
% 19.77/3.00                [status(thm)],
% 19.77/3.00                [c_1584,c_30,c_31,c_36,c_1092,c_1297]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_2498,plain,
% 19.77/3.00      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_812,c_2492]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_19,negated_conjecture,
% 19.77/3.00      ( m1_pre_topc(sK3,sK0) ),
% 19.77/3.00      inference(cnf_transformation,[],[f57]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_303,negated_conjecture,
% 19.77/3.00      ( m1_pre_topc(sK3,sK0) ),
% 19.77/3.00      inference(subtyping,[status(esa)],[c_19]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_816,plain,
% 19.77/3.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_303]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_12,negated_conjecture,
% 19.77/3.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 19.77/3.00      inference(cnf_transformation,[],[f64]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_310,negated_conjecture,
% 19.77/3.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 19.77/3.00      inference(subtyping,[status(esa)],[c_12]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_809,plain,
% 19.77/3.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_310]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_5,plain,
% 19.77/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.77/3.00      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 19.77/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.77/3.00      | ~ m1_pre_topc(X4,X3)
% 19.77/3.00      | ~ m1_pre_topc(X1,X3)
% 19.77/3.00      | v2_struct_0(X3)
% 19.77/3.00      | v2_struct_0(X2)
% 19.77/3.00      | ~ v1_funct_1(X0)
% 19.77/3.00      | ~ l1_pre_topc(X3)
% 19.77/3.00      | ~ l1_pre_topc(X2)
% 19.77/3.00      | ~ v2_pre_topc(X3)
% 19.77/3.00      | ~ v2_pre_topc(X2) ),
% 19.77/3.00      inference(cnf_transformation,[],[f42]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_317,plain,
% 19.77/3.00      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 19.77/3.00      | v1_funct_2(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),u1_struct_0(X3_48),u1_struct_0(X1_48))
% 19.77/3.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 19.77/3.00      | ~ m1_pre_topc(X3_48,X2_48)
% 19.77/3.00      | ~ m1_pre_topc(X0_48,X2_48)
% 19.77/3.00      | v2_struct_0(X1_48)
% 19.77/3.00      | v2_struct_0(X2_48)
% 19.77/3.00      | ~ v1_funct_1(X0_49)
% 19.77/3.00      | ~ l1_pre_topc(X1_48)
% 19.77/3.00      | ~ l1_pre_topc(X2_48)
% 19.77/3.00      | ~ v2_pre_topc(X1_48)
% 19.77/3.00      | ~ v2_pre_topc(X2_48) ),
% 19.77/3.00      inference(subtyping,[status(esa)],[c_5]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_802,plain,
% 19.77/3.00      ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 19.77/3.00      | v1_funct_2(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),u1_struct_0(X3_48),u1_struct_0(X1_48)) = iProver_top
% 19.77/3.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 19.77/3.00      | m1_pre_topc(X3_48,X2_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,X2_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | v2_struct_0(X2_48) = iProver_top
% 19.77/3.00      | v1_funct_1(X0_49) != iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(X2_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X2_48) != iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_4,plain,
% 19.77/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.77/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.77/3.00      | m1_subset_1(k3_tmap_1(X3,X2,X1,X4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 19.77/3.00      | ~ m1_pre_topc(X4,X3)
% 19.77/3.00      | ~ m1_pre_topc(X1,X3)
% 19.77/3.00      | v2_struct_0(X3)
% 19.77/3.00      | v2_struct_0(X2)
% 19.77/3.00      | ~ v1_funct_1(X0)
% 19.77/3.00      | ~ l1_pre_topc(X3)
% 19.77/3.00      | ~ l1_pre_topc(X2)
% 19.77/3.00      | ~ v2_pre_topc(X3)
% 19.77/3.00      | ~ v2_pre_topc(X2) ),
% 19.77/3.00      inference(cnf_transformation,[],[f43]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_318,plain,
% 19.77/3.00      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 19.77/3.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 19.77/3.00      | m1_subset_1(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48))))
% 19.77/3.00      | ~ m1_pre_topc(X3_48,X2_48)
% 19.77/3.00      | ~ m1_pre_topc(X0_48,X2_48)
% 19.77/3.00      | v2_struct_0(X1_48)
% 19.77/3.00      | v2_struct_0(X2_48)
% 19.77/3.00      | ~ v1_funct_1(X0_49)
% 19.77/3.00      | ~ l1_pre_topc(X1_48)
% 19.77/3.00      | ~ l1_pre_topc(X2_48)
% 19.77/3.00      | ~ v2_pre_topc(X1_48)
% 19.77/3.00      | ~ v2_pre_topc(X2_48) ),
% 19.77/3.00      inference(subtyping,[status(esa)],[c_4]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_801,plain,
% 19.77/3.00      ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 19.77/3.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 19.77/3.00      | m1_subset_1(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) = iProver_top
% 19.77/3.00      | m1_pre_topc(X3_48,X2_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,X2_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | v2_struct_0(X2_48) = iProver_top
% 19.77/3.00      | v1_funct_1(X0_49) != iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(X2_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X2_48) != iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_3,plain,
% 19.77/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.77/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.77/3.00      | ~ m1_pre_topc(X3,X4)
% 19.77/3.00      | ~ m1_pre_topc(X3,X1)
% 19.77/3.00      | ~ m1_pre_topc(X1,X4)
% 19.77/3.00      | v2_struct_0(X4)
% 19.77/3.00      | v2_struct_0(X2)
% 19.77/3.00      | ~ v1_funct_1(X0)
% 19.77/3.00      | ~ l1_pre_topc(X4)
% 19.77/3.00      | ~ l1_pre_topc(X2)
% 19.77/3.00      | ~ v2_pre_topc(X4)
% 19.77/3.00      | ~ v2_pre_topc(X2)
% 19.77/3.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 19.77/3.00      inference(cnf_transformation,[],[f40]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_319,plain,
% 19.77/3.00      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 19.77/3.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 19.77/3.00      | ~ m1_pre_topc(X2_48,X0_48)
% 19.77/3.00      | ~ m1_pre_topc(X0_48,X3_48)
% 19.77/3.00      | ~ m1_pre_topc(X2_48,X3_48)
% 19.77/3.00      | v2_struct_0(X3_48)
% 19.77/3.00      | v2_struct_0(X1_48)
% 19.77/3.00      | ~ v1_funct_1(X0_49)
% 19.77/3.00      | ~ l1_pre_topc(X1_48)
% 19.77/3.00      | ~ l1_pre_topc(X3_48)
% 19.77/3.00      | ~ v2_pre_topc(X1_48)
% 19.77/3.00      | ~ v2_pre_topc(X3_48)
% 19.77/3.00      | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49) ),
% 19.77/3.00      inference(subtyping,[status(esa)],[c_3]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_800,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49)
% 19.77/3.00      | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 19.77/3.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 19.77/3.00      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,X3_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X2_48,X3_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X3_48) = iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | v1_funct_1(X0_49) != iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(X3_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X3_48) != iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_319]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_2189,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X4_48)) = k3_tmap_1(X5_48,X1_48,X0_48,X4_48,k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49))
% 19.77/3.00      | v1_funct_2(X0_49,u1_struct_0(X3_48),u1_struct_0(X1_48)) != iProver_top
% 19.77/3.00      | v1_funct_2(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 19.77/3.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) != iProver_top
% 19.77/3.00      | m1_pre_topc(X3_48,X2_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,X2_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X4_48,X0_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,X5_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X4_48,X5_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X2_48) = iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | v2_struct_0(X5_48) = iProver_top
% 19.77/3.00      | v1_funct_1(X0_49) != iProver_top
% 19.77/3.00      | v1_funct_1(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49)) != iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(X2_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(X5_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X2_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X5_48) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_801,c_800]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_4014,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X4_48)) = k3_tmap_1(X5_48,X1_48,X0_48,X4_48,k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49))
% 19.77/3.00      | v1_funct_2(X0_49,u1_struct_0(X3_48),u1_struct_0(X1_48)) != iProver_top
% 19.77/3.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) != iProver_top
% 19.77/3.00      | m1_pre_topc(X3_48,X2_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,X2_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X4_48,X0_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,X5_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X4_48,X5_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X2_48) = iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | v2_struct_0(X5_48) = iProver_top
% 19.77/3.00      | v1_funct_1(X0_49) != iProver_top
% 19.77/3.00      | v1_funct_1(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49)) != iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(X2_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(X5_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X2_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X5_48) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_802,c_2189]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_7311,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),u1_struct_0(X2_48)) = k3_tmap_1(X3_48,sK1,X0_48,X2_48,k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5))
% 19.77/3.00      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,X3_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X2_48,X3_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK2,X1_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X3_48) = iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | v2_struct_0(sK1) = iProver_top
% 19.77/3.00      | v1_funct_1(k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)) != iProver_top
% 19.77/3.00      | v1_funct_1(sK5) != iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(X3_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK1) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X3_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK1) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_809,c_4014]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_25,negated_conjecture,
% 19.77/3.00      ( ~ v2_struct_0(sK1) ),
% 19.77/3.00      inference(cnf_transformation,[],[f51]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_32,plain,
% 19.77/3.00      ( v2_struct_0(sK1) != iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_24,negated_conjecture,
% 19.77/3.00      ( v2_pre_topc(sK1) ),
% 19.77/3.00      inference(cnf_transformation,[],[f52]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_33,plain,
% 19.77/3.00      ( v2_pre_topc(sK1) = iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_23,negated_conjecture,
% 19.77/3.00      ( l1_pre_topc(sK1) ),
% 19.77/3.00      inference(cnf_transformation,[],[f53]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_34,plain,
% 19.77/3.00      ( l1_pre_topc(sK1) = iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_14,negated_conjecture,
% 19.77/3.00      ( v1_funct_1(sK5) ),
% 19.77/3.00      inference(cnf_transformation,[],[f62]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_43,plain,
% 19.77/3.00      ( v1_funct_1(sK5) = iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_13,negated_conjecture,
% 19.77/3.00      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 19.77/3.00      inference(cnf_transformation,[],[f63]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_44,plain,
% 19.77/3.00      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_6,plain,
% 19.77/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.77/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.77/3.00      | ~ m1_pre_topc(X3,X4)
% 19.77/3.00      | ~ m1_pre_topc(X1,X4)
% 19.77/3.00      | v2_struct_0(X4)
% 19.77/3.00      | v2_struct_0(X2)
% 19.77/3.00      | ~ v1_funct_1(X0)
% 19.77/3.00      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0))
% 19.77/3.00      | ~ l1_pre_topc(X4)
% 19.77/3.00      | ~ l1_pre_topc(X2)
% 19.77/3.00      | ~ v2_pre_topc(X4)
% 19.77/3.00      | ~ v2_pre_topc(X2) ),
% 19.77/3.00      inference(cnf_transformation,[],[f41]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_316,plain,
% 19.77/3.00      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 19.77/3.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 19.77/3.00      | ~ m1_pre_topc(X0_48,X2_48)
% 19.77/3.00      | ~ m1_pre_topc(X3_48,X2_48)
% 19.77/3.00      | v2_struct_0(X2_48)
% 19.77/3.00      | v2_struct_0(X1_48)
% 19.77/3.00      | ~ v1_funct_1(X0_49)
% 19.77/3.00      | v1_funct_1(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49))
% 19.77/3.00      | ~ l1_pre_topc(X1_48)
% 19.77/3.00      | ~ l1_pre_topc(X2_48)
% 19.77/3.00      | ~ v2_pre_topc(X1_48)
% 19.77/3.00      | ~ v2_pre_topc(X2_48) ),
% 19.77/3.00      inference(subtyping,[status(esa)],[c_6]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_803,plain,
% 19.77/3.00      ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 19.77/3.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 19.77/3.00      | m1_pre_topc(X2_48,X3_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,X3_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | v2_struct_0(X3_48) = iProver_top
% 19.77/3.00      | v1_funct_1(X0_49) != iProver_top
% 19.77/3.00      | v1_funct_1(k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49)) = iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(X3_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X3_48) != iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_1820,plain,
% 19.77/3.00      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK2,X1_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | v2_struct_0(sK1) = iProver_top
% 19.77/3.00      | v1_funct_1(k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)) = iProver_top
% 19.77/3.00      | v1_funct_1(sK5) != iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK1) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK1) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_809,c_803]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_2893,plain,
% 19.77/3.00      ( v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v1_funct_1(k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)) = iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK2,X1_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top ),
% 19.77/3.00      inference(global_propositional_subsumption,
% 19.77/3.00                [status(thm)],
% 19.77/3.00                [c_1820,c_32,c_33,c_34,c_43,c_44]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_2894,plain,
% 19.77/3.00      ( m1_pre_topc(X0_48,X1_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK2,X1_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | v1_funct_1(k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)) = iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top ),
% 19.77/3.00      inference(renaming,[status(thm)],[c_2893]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_7663,plain,
% 19.77/3.00      ( v2_pre_topc(X3_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | v2_struct_0(X3_48) = iProver_top
% 19.77/3.00      | m1_pre_topc(sK2,X1_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X2_48,X3_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,X3_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 19.77/3.00      | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),u1_struct_0(X2_48)) = k3_tmap_1(X3_48,sK1,X0_48,X2_48,k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5))
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(X3_48) != iProver_top ),
% 19.77/3.00      inference(global_propositional_subsumption,
% 19.77/3.00                [status(thm)],
% 19.77/3.00                [c_7311,c_32,c_33,c_34,c_43,c_44,c_2894]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_7664,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),u1_struct_0(X2_48)) = k3_tmap_1(X3_48,sK1,X0_48,X2_48,k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5))
% 19.77/3.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,X3_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X2_48,X3_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK2,X1_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X3_48) = iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(X3_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X3_48) != iProver_top ),
% 19.77/3.00      inference(renaming,[status(thm)],[c_7663]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_7672,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5))
% 19.77/3.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,sK3) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK3,X1_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | v2_struct_0(sK0) = iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK0) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK0) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_816,c_7664]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_2120,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)
% 19.77/3.00      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,sK2) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK2,X1_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | v2_struct_0(sK1) = iProver_top
% 19.77/3.00      | v1_funct_1(sK5) != iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK1) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK1) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_809,c_800]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_3201,plain,
% 19.77/3.00      ( v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)
% 19.77/3.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,sK2) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK2,X1_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top ),
% 19.77/3.00      inference(global_propositional_subsumption,
% 19.77/3.00                [status(thm)],
% 19.77/3.00                [c_2120,c_32,c_33,c_34,c_43,c_44]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_3202,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)
% 19.77/3.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,sK2) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK2,X1_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top ),
% 19.77/3.00      inference(renaming,[status(thm)],[c_3201]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_3210,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK2,sK3,sK5)
% 19.77/3.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 19.77/3.00      | v2_struct_0(sK0) = iProver_top
% 19.77/3.00      | l1_pre_topc(sK0) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK0) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_816,c_3202]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_2,plain,
% 19.77/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.77/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.77/3.00      | ~ m1_pre_topc(X3,X1)
% 19.77/3.00      | v2_struct_0(X1)
% 19.77/3.00      | v2_struct_0(X2)
% 19.77/3.00      | ~ v1_funct_1(X0)
% 19.77/3.00      | ~ l1_pre_topc(X1)
% 19.77/3.00      | ~ l1_pre_topc(X2)
% 19.77/3.00      | ~ v2_pre_topc(X1)
% 19.77/3.00      | ~ v2_pre_topc(X2)
% 19.77/3.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 19.77/3.00      inference(cnf_transformation,[],[f39]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_320,plain,
% 19.77/3.00      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 19.77/3.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 19.77/3.00      | ~ m1_pre_topc(X2_48,X0_48)
% 19.77/3.00      | v2_struct_0(X1_48)
% 19.77/3.00      | v2_struct_0(X0_48)
% 19.77/3.00      | ~ v1_funct_1(X0_49)
% 19.77/3.00      | ~ l1_pre_topc(X1_48)
% 19.77/3.00      | ~ l1_pre_topc(X0_48)
% 19.77/3.00      | ~ v2_pre_topc(X1_48)
% 19.77/3.00      | ~ v2_pre_topc(X0_48)
% 19.77/3.00      | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k2_tmap_1(X0_48,X1_48,X0_49,X2_48) ),
% 19.77/3.00      inference(subtyping,[status(esa)],[c_2]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_799,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k2_tmap_1(X0_48,X1_48,X0_49,X2_48)
% 19.77/3.00      | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 19.77/3.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 19.77/3.00      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | v2_struct_0(X0_48) = iProver_top
% 19.77/3.00      | v1_funct_1(X0_49) != iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(X0_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X0_48) != iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_320]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_1815,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK5,X0_48)
% 19.77/3.00      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,sK2) != iProver_top
% 19.77/3.00      | v2_struct_0(sK2) = iProver_top
% 19.77/3.00      | v2_struct_0(sK1) = iProver_top
% 19.77/3.00      | v1_funct_1(sK5) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK2) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK1) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK2) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK1) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_809,c_799]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_22,negated_conjecture,
% 19.77/3.00      ( ~ v2_struct_0(sK2) ),
% 19.77/3.00      inference(cnf_transformation,[],[f54]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_35,plain,
% 19.77/3.00      ( v2_struct_0(sK2) != iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_2771,plain,
% 19.77/3.00      ( m1_pre_topc(X0_48,sK2) != iProver_top
% 19.77/3.00      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK5,X0_48) ),
% 19.77/3.00      inference(global_propositional_subsumption,
% 19.77/3.00                [status(thm)],
% 19.77/3.00                [c_1815,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_43,c_44,
% 19.77/3.00                 c_1092,c_1297]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_2772,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK5,X0_48)
% 19.77/3.00      | m1_pre_topc(X0_48,sK2) != iProver_top ),
% 19.77/3.00      inference(renaming,[status(thm)],[c_2771]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_2777,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_813,c_2772]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_3216,plain,
% 19.77/3.00      ( k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3)
% 19.77/3.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 19.77/3.00      | v2_struct_0(sK0) = iProver_top
% 19.77/3.00      | l1_pre_topc(sK0) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK0) != iProver_top ),
% 19.77/3.00      inference(light_normalisation,[status(thm)],[c_3210,c_2777]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_28,negated_conjecture,
% 19.77/3.00      ( ~ v2_struct_0(sK0) ),
% 19.77/3.00      inference(cnf_transformation,[],[f48]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_29,plain,
% 19.77/3.00      ( v2_struct_0(sK0) != iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_41,plain,
% 19.77/3.00      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_3804,plain,
% 19.77/3.00      ( k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
% 19.77/3.00      inference(global_propositional_subsumption,
% 19.77/3.00                [status(thm)],
% 19.77/3.00                [c_3216,c_29,c_30,c_31,c_36,c_41]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_7678,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3))
% 19.77/3.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,sK3) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK3,X1_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | v2_struct_0(sK0) = iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK0) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK0) != iProver_top ),
% 19.77/3.00      inference(light_normalisation,[status(thm)],[c_7672,c_3804]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_7,plain,
% 19.77/3.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 19.77/3.00      inference(cnf_transformation,[],[f44]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_315,plain,
% 19.77/3.00      ( m1_pre_topc(X0_48,X0_48) | ~ l1_pre_topc(X0_48) ),
% 19.77/3.00      inference(subtyping,[status(esa)],[c_7]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_1228,plain,
% 19.77/3.00      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 19.77/3.00      inference(instantiation,[status(thm)],[c_315]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_1229,plain,
% 19.77/3.00      ( m1_pre_topc(sK2,sK2) = iProver_top
% 19.77/3.00      | l1_pre_topc(sK2) != iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_1228]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_7670,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k3_tmap_1(sK2,sK1,sK2,sK3,sK5))
% 19.77/3.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,sK3) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK3,X1_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | v2_struct_0(sK2) = iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK2) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK2) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_813,c_7664]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_3208,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k3_tmap_1(sK2,sK1,sK2,sK3,sK5)
% 19.77/3.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 19.77/3.00      | v2_struct_0(sK2) = iProver_top
% 19.77/3.00      | l1_pre_topc(sK2) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK2) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_813,c_3202]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_3218,plain,
% 19.77/3.00      ( k3_tmap_1(sK2,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3)
% 19.77/3.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 19.77/3.00      | v2_struct_0(sK2) = iProver_top
% 19.77/3.00      | l1_pre_topc(sK2) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK2) != iProver_top ),
% 19.77/3.00      inference(light_normalisation,[status(thm)],[c_3208,c_2777]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_4665,plain,
% 19.77/3.00      ( k3_tmap_1(sK2,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
% 19.77/3.00      inference(global_propositional_subsumption,
% 19.77/3.00                [status(thm)],
% 19.77/3.00                [c_3218,c_30,c_31,c_35,c_36,c_41,c_1092,c_1229,c_1297]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_7680,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3))
% 19.77/3.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,sK3) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK3,X1_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | v2_struct_0(sK2) = iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK2) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK2) != iProver_top ),
% 19.77/3.00      inference(light_normalisation,[status(thm)],[c_7670,c_4665]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_9937,plain,
% 19.77/3.00      ( v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | m1_pre_topc(sK3,X1_48) != iProver_top
% 19.77/3.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3))
% 19.77/3.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,sK3) != iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top ),
% 19.77/3.00      inference(global_propositional_subsumption,
% 19.77/3.00                [status(thm)],
% 19.77/3.00                [c_7678,c_30,c_31,c_35,c_36,c_1092,c_1229,c_1297,c_7680]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_9938,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3))
% 19.77/3.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,sK3) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK3,X1_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top ),
% 19.77/3.00      inference(renaming,[status(thm)],[c_9937]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_9949,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3))
% 19.77/3.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK4,sK3) != iProver_top
% 19.77/3.00      | v2_struct_0(sK2) = iProver_top
% 19.77/3.00      | l1_pre_topc(sK2) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK2) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_2498,c_9938]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_3808,plain,
% 19.77/3.00      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.77/3.00      | m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 19.77/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 19.77/3.00      | v2_struct_0(sK0) = iProver_top
% 19.77/3.00      | v2_struct_0(sK1) = iProver_top
% 19.77/3.00      | v1_funct_1(sK5) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK0) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK1) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK0) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK1) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_3804,c_801]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_38,plain,
% 19.77/3.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_45,plain,
% 19.77/3.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_5658,plain,
% 19.77/3.00      ( m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 19.77/3.00      inference(global_propositional_subsumption,
% 19.77/3.00                [status(thm)],
% 19.77/3.00                [c_3808,c_29,c_30,c_31,c_32,c_33,c_34,c_36,c_38,c_43,
% 19.77/3.00                 c_44,c_45]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_5664,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X0_48)
% 19.77/3.00      | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,sK3) != iProver_top
% 19.77/3.00      | v2_struct_0(sK3) = iProver_top
% 19.77/3.00      | v2_struct_0(sK1) = iProver_top
% 19.77/3.00      | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK3) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK1) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK3) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK1) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_5658,c_799]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_20,negated_conjecture,
% 19.77/3.00      ( ~ v2_struct_0(sK3) ),
% 19.77/3.00      inference(cnf_transformation,[],[f56]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_37,plain,
% 19.77/3.00      ( v2_struct_0(sK3) != iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_1240,plain,
% 19.77/3.00      ( ~ m1_pre_topc(sK3,X0_48)
% 19.77/3.00      | ~ l1_pre_topc(X0_48)
% 19.77/3.00      | l1_pre_topc(sK3) ),
% 19.77/3.00      inference(instantiation,[status(thm)],[c_321]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_1241,plain,
% 19.77/3.00      ( m1_pre_topc(sK3,X0_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(X0_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK3) = iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_1240]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_1243,plain,
% 19.77/3.00      ( m1_pre_topc(sK3,sK0) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK3) = iProver_top
% 19.77/3.00      | l1_pre_topc(sK0) != iProver_top ),
% 19.77/3.00      inference(instantiation,[status(thm)],[c_1241]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_797,plain,
% 19.77/3.00      ( m1_pre_topc(X0_48,X1_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X0_48) = iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_322]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_1263,plain,
% 19.77/3.00      ( l1_pre_topc(sK0) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK3) = iProver_top
% 19.77/3.00      | v2_pre_topc(sK0) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_816,c_797]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_3809,plain,
% 19.77/3.00      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 19.77/3.00      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.77/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 19.77/3.00      | v2_struct_0(sK0) = iProver_top
% 19.77/3.00      | v2_struct_0(sK1) = iProver_top
% 19.77/3.00      | v1_funct_1(sK5) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK0) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK1) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK0) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK1) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_3804,c_802]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_3810,plain,
% 19.77/3.00      ( m1_pre_topc(sK2,sK0) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 19.77/3.00      | v2_struct_0(sK0) = iProver_top
% 19.77/3.00      | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) = iProver_top
% 19.77/3.00      | l1_pre_topc(sK0) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK0) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_3804,c_2894]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_6182,plain,
% 19.77/3.00      ( m1_pre_topc(X0_48,sK3) != iProver_top
% 19.77/3.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X0_48) ),
% 19.77/3.00      inference(global_propositional_subsumption,
% 19.77/3.00                [status(thm)],
% 19.77/3.00                [c_5664,c_29,c_30,c_31,c_32,c_33,c_34,c_36,c_37,c_38,
% 19.77/3.00                 c_43,c_44,c_45,c_1243,c_1263,c_3809,c_3810]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_6183,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X0_48)
% 19.77/3.00      | m1_pre_topc(X0_48,sK3) != iProver_top ),
% 19.77/3.00      inference(renaming,[status(thm)],[c_6182]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_6188,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_812,c_6183]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_9950,plain,
% 19.77/3.00      ( k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
% 19.77/3.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK4,sK3) != iProver_top
% 19.77/3.00      | v2_struct_0(sK2) = iProver_top
% 19.77/3.00      | l1_pre_topc(sK2) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK2) != iProver_top ),
% 19.77/3.00      inference(light_normalisation,[status(thm)],[c_9949,c_6188]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_42,plain,
% 19.77/3.00      ( m1_pre_topc(sK4,sK3) = iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_10203,plain,
% 19.77/3.00      ( k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
% 19.77/3.00      inference(global_propositional_subsumption,
% 19.77/3.00                [status(thm)],
% 19.77/3.00                [c_9950,c_30,c_31,c_35,c_36,c_41,c_42,c_1092,c_1297]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_301,negated_conjecture,
% 19.77/3.00      ( m1_pre_topc(sK2,sK0) ),
% 19.77/3.00      inference(subtyping,[status(esa)],[c_21]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_818,plain,
% 19.77/3.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_301]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_3211,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK2,sK2,sK5)
% 19.77/3.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 19.77/3.00      | v2_struct_0(sK0) = iProver_top
% 19.77/3.00      | l1_pre_topc(sK0) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK0) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_818,c_3202]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_804,plain,
% 19.77/3.00      ( m1_pre_topc(X0_48,X0_48) = iProver_top
% 19.77/3.00      | l1_pre_topc(X0_48) != iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_315]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_2778,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK5,sK2)
% 19.77/3.00      | l1_pre_topc(sK2) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_804,c_2772]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_1091,plain,
% 19.77/3.00      ( ~ m1_pre_topc(sK2,sK0) | l1_pre_topc(sK2) | ~ l1_pre_topc(sK0) ),
% 19.77/3.00      inference(instantiation,[status(thm)],[c_1089]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_1296,plain,
% 19.77/3.00      ( ~ m1_pre_topc(sK2,sK0)
% 19.77/3.00      | ~ l1_pre_topc(sK0)
% 19.77/3.00      | v2_pre_topc(sK2)
% 19.77/3.00      | ~ v2_pre_topc(sK0) ),
% 19.77/3.00      inference(instantiation,[status(thm)],[c_1294]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_906,plain,
% 19.77/3.00      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(sK1))
% 19.77/3.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(sK1))))
% 19.77/3.00      | ~ m1_pre_topc(X1_48,X0_48)
% 19.77/3.00      | v2_struct_0(X0_48)
% 19.77/3.00      | v2_struct_0(sK1)
% 19.77/3.00      | ~ v1_funct_1(X0_49)
% 19.77/3.00      | ~ l1_pre_topc(X0_48)
% 19.77/3.00      | ~ l1_pre_topc(sK1)
% 19.77/3.00      | ~ v2_pre_topc(X0_48)
% 19.77/3.00      | ~ v2_pre_topc(sK1)
% 19.77/3.00      | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49,u1_struct_0(X1_48)) = k2_tmap_1(X0_48,sK1,X0_49,X1_48) ),
% 19.77/3.00      inference(instantiation,[status(thm)],[c_320]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_1450,plain,
% 19.77/3.00      ( ~ v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(sK1))
% 19.77/3.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 19.77/3.00      | ~ m1_pre_topc(X0_48,sK2)
% 19.77/3.00      | v2_struct_0(sK2)
% 19.77/3.00      | v2_struct_0(sK1)
% 19.77/3.00      | ~ v1_funct_1(X0_49)
% 19.77/3.00      | ~ l1_pre_topc(sK2)
% 19.77/3.00      | ~ l1_pre_topc(sK1)
% 19.77/3.00      | ~ v2_pre_topc(sK2)
% 19.77/3.00      | ~ v2_pre_topc(sK1)
% 19.77/3.00      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_49,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,X0_49,X0_48) ),
% 19.77/3.00      inference(instantiation,[status(thm)],[c_906]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_2001,plain,
% 19.77/3.00      ( ~ v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(sK1))
% 19.77/3.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 19.77/3.00      | ~ m1_pre_topc(sK2,sK2)
% 19.77/3.00      | v2_struct_0(sK2)
% 19.77/3.00      | v2_struct_0(sK1)
% 19.77/3.00      | ~ v1_funct_1(X0_49)
% 19.77/3.00      | ~ l1_pre_topc(sK2)
% 19.77/3.00      | ~ l1_pre_topc(sK1)
% 19.77/3.00      | ~ v2_pre_topc(sK2)
% 19.77/3.00      | ~ v2_pre_topc(sK1)
% 19.77/3.00      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_49,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,X0_49,sK2) ),
% 19.77/3.00      inference(instantiation,[status(thm)],[c_1450]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_2003,plain,
% 19.77/3.00      ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
% 19.77/3.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 19.77/3.00      | ~ m1_pre_topc(sK2,sK2)
% 19.77/3.00      | v2_struct_0(sK2)
% 19.77/3.00      | v2_struct_0(sK1)
% 19.77/3.00      | ~ v1_funct_1(sK5)
% 19.77/3.00      | ~ l1_pre_topc(sK2)
% 19.77/3.00      | ~ l1_pre_topc(sK1)
% 19.77/3.00      | ~ v2_pre_topc(sK2)
% 19.77/3.00      | ~ v2_pre_topc(sK1)
% 19.77/3.00      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK5,sK2) ),
% 19.77/3.00      inference(instantiation,[status(thm)],[c_2001]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_3052,plain,
% 19.77/3.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK5,sK2) ),
% 19.77/3.00      inference(global_propositional_subsumption,
% 19.77/3.00                [status(thm)],
% 19.77/3.00                [c_2778,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_14,c_13,
% 19.77/3.00                 c_12,c_1091,c_1228,c_1296,c_2003]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_3215,plain,
% 19.77/3.00      ( k3_tmap_1(sK0,sK1,sK2,sK2,sK5) = k2_tmap_1(sK2,sK1,sK5,sK2)
% 19.77/3.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 19.77/3.00      | v2_struct_0(sK0) = iProver_top
% 19.77/3.00      | l1_pre_topc(sK0) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK0) != iProver_top ),
% 19.77/3.00      inference(light_normalisation,[status(thm)],[c_3211,c_3052]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_3606,plain,
% 19.77/3.00      ( k3_tmap_1(sK0,sK1,sK2,sK2,sK5) = k2_tmap_1(sK2,sK1,sK5,sK2) ),
% 19.77/3.00      inference(global_propositional_subsumption,
% 19.77/3.00                [status(thm)],
% 19.77/3.00                [c_3215,c_29,c_30,c_31,c_36,c_1092,c_1229]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_8,plain,
% 19.77/3.00      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
% 19.77/3.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 19.77/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 19.77/3.00      | ~ m1_pre_topc(X0,X3)
% 19.77/3.00      | v2_struct_0(X3)
% 19.77/3.00      | v2_struct_0(X1)
% 19.77/3.00      | v2_struct_0(X0)
% 19.77/3.00      | ~ v1_funct_1(X2)
% 19.77/3.00      | ~ l1_pre_topc(X3)
% 19.77/3.00      | ~ l1_pre_topc(X1)
% 19.77/3.00      | ~ v2_pre_topc(X3)
% 19.77/3.00      | ~ v2_pre_topc(X1) ),
% 19.77/3.00      inference(cnf_transformation,[],[f45]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_314,plain,
% 19.77/3.00      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,k3_tmap_1(X2_48,X1_48,X0_48,X0_48,X0_49))
% 19.77/3.00      | ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 19.77/3.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 19.77/3.00      | ~ m1_pre_topc(X0_48,X2_48)
% 19.77/3.00      | v2_struct_0(X1_48)
% 19.77/3.00      | v2_struct_0(X0_48)
% 19.77/3.00      | v2_struct_0(X2_48)
% 19.77/3.00      | ~ v1_funct_1(X0_49)
% 19.77/3.00      | ~ l1_pre_topc(X1_48)
% 19.77/3.00      | ~ l1_pre_topc(X2_48)
% 19.77/3.00      | ~ v2_pre_topc(X1_48)
% 19.77/3.00      | ~ v2_pre_topc(X2_48) ),
% 19.77/3.00      inference(subtyping,[status(esa)],[c_8]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_805,plain,
% 19.77/3.00      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,k3_tmap_1(X2_48,X1_48,X0_48,X0_48,X0_49)) = iProver_top
% 19.77/3.00      | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 19.77/3.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,X2_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | v2_struct_0(X0_48) = iProver_top
% 19.77/3.00      | v2_struct_0(X2_48) = iProver_top
% 19.77/3.00      | v1_funct_1(X0_49) != iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(X2_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X2_48) != iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_3610,plain,
% 19.77/3.00      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2)) = iProver_top
% 19.77/3.00      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.77/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 19.77/3.00      | v2_struct_0(sK2) = iProver_top
% 19.77/3.00      | v2_struct_0(sK0) = iProver_top
% 19.77/3.00      | v2_struct_0(sK1) = iProver_top
% 19.77/3.00      | v1_funct_1(sK5) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK0) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK1) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK0) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK1) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_3606,c_805]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_4428,plain,
% 19.77/3.00      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_tmap_1(sK2,sK1,sK5,sK2)) = iProver_top ),
% 19.77/3.00      inference(global_propositional_subsumption,
% 19.77/3.00                [status(thm)],
% 19.77/3.00                [c_3610,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_43,
% 19.77/3.00                 c_44,c_45]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_9,plain,
% 19.77/3.00      ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_tmap_1(X3,X1,X4,X0))
% 19.77/3.00      | r2_funct_2(u1_struct_0(X5),u1_struct_0(X1),k3_tmap_1(X3,X1,X0,X5,X2),k2_tmap_1(X3,X1,X4,X5))
% 19.77/3.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 19.77/3.00      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
% 19.77/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 19.77/3.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 19.77/3.00      | ~ m1_pre_topc(X5,X3)
% 19.77/3.00      | ~ m1_pre_topc(X5,X0)
% 19.77/3.00      | ~ m1_pre_topc(X0,X3)
% 19.77/3.00      | v2_struct_0(X3)
% 19.77/3.00      | v2_struct_0(X1)
% 19.77/3.00      | v2_struct_0(X0)
% 19.77/3.00      | v2_struct_0(X5)
% 19.77/3.00      | ~ v1_funct_1(X4)
% 19.77/3.00      | ~ v1_funct_1(X2)
% 19.77/3.00      | ~ l1_pre_topc(X3)
% 19.77/3.00      | ~ l1_pre_topc(X1)
% 19.77/3.00      | ~ v2_pre_topc(X3)
% 19.77/3.00      | ~ v2_pre_topc(X1) ),
% 19.77/3.00      inference(cnf_transformation,[],[f46]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_313,plain,
% 19.77/3.00      ( ~ r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,k2_tmap_1(X2_48,X1_48,X1_49,X0_48))
% 19.77/3.00      | r2_funct_2(u1_struct_0(X3_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k2_tmap_1(X2_48,X1_48,X1_49,X3_48))
% 19.77/3.00      | ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 19.77/3.00      | ~ v1_funct_2(X1_49,u1_struct_0(X2_48),u1_struct_0(X1_48))
% 19.77/3.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 19.77/3.00      | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48))))
% 19.77/3.00      | ~ m1_pre_topc(X3_48,X2_48)
% 19.77/3.00      | ~ m1_pre_topc(X3_48,X0_48)
% 19.77/3.00      | ~ m1_pre_topc(X0_48,X2_48)
% 19.77/3.00      | v2_struct_0(X3_48)
% 19.77/3.00      | v2_struct_0(X1_48)
% 19.77/3.00      | v2_struct_0(X0_48)
% 19.77/3.00      | v2_struct_0(X2_48)
% 19.77/3.00      | ~ v1_funct_1(X1_49)
% 19.77/3.00      | ~ v1_funct_1(X0_49)
% 19.77/3.00      | ~ l1_pre_topc(X1_48)
% 19.77/3.00      | ~ l1_pre_topc(X2_48)
% 19.77/3.00      | ~ v2_pre_topc(X1_48)
% 19.77/3.00      | ~ v2_pre_topc(X2_48) ),
% 19.77/3.00      inference(subtyping,[status(esa)],[c_9]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_806,plain,
% 19.77/3.00      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,k2_tmap_1(X2_48,X1_48,X1_49,X0_48)) != iProver_top
% 19.77/3.00      | r2_funct_2(u1_struct_0(X3_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k2_tmap_1(X2_48,X1_48,X1_49,X3_48)) = iProver_top
% 19.77/3.00      | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 19.77/3.00      | v1_funct_2(X1_49,u1_struct_0(X2_48),u1_struct_0(X1_48)) != iProver_top
% 19.77/3.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 19.77/3.00      | m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48)))) != iProver_top
% 19.77/3.00      | m1_pre_topc(X3_48,X0_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X3_48,X2_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,X2_48) != iProver_top
% 19.77/3.00      | v2_struct_0(X3_48) = iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | v2_struct_0(X0_48) = iProver_top
% 19.77/3.00      | v2_struct_0(X2_48) = iProver_top
% 19.77/3.00      | v1_funct_1(X0_49) != iProver_top
% 19.77/3.00      | v1_funct_1(X1_49) != iProver_top
% 19.77/3.00      | l1_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | l1_pre_topc(X2_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X1_48) != iProver_top
% 19.77/3.00      | v2_pre_topc(X2_48) != iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_4432,plain,
% 19.77/3.00      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0_48,sK5),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
% 19.77/3.00      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.77/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,sK2) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.77/3.00      | v2_struct_0(X0_48) = iProver_top
% 19.77/3.00      | v2_struct_0(sK2) = iProver_top
% 19.77/3.00      | v2_struct_0(sK1) = iProver_top
% 19.77/3.00      | v1_funct_1(sK5) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK2) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK1) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK2) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK1) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_4428,c_806]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_12836,plain,
% 19.77/3.00      ( v2_struct_0(X0_48) = iProver_top
% 19.77/3.00      | r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0_48,sK5),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,sK2) != iProver_top ),
% 19.77/3.00      inference(global_propositional_subsumption,
% 19.77/3.00                [status(thm)],
% 19.77/3.00                [c_4432,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_43,c_44,
% 19.77/3.00                 c_45,c_1092,c_1229,c_1297]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_12837,plain,
% 19.77/3.00      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK2,X0_48,sK5),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,sK2) != iProver_top
% 19.77/3.00      | v2_struct_0(X0_48) = iProver_top ),
% 19.77/3.00      inference(renaming,[status(thm)],[c_12836]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_12843,plain,
% 19.77/3.00      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3)) = iProver_top
% 19.77/3.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 19.77/3.00      | v2_struct_0(sK3) = iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_4665,c_12837]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_13378,plain,
% 19.77/3.00      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3)) = iProver_top ),
% 19.77/3.00      inference(global_propositional_subsumption,
% 19.77/3.00                [status(thm)],
% 19.77/3.00                [c_12843,c_37,c_41]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_13382,plain,
% 19.77/3.00      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
% 19.77/3.00      | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 19.77/3.00      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.77/3.00      | m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 19.77/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,sK2) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,sK3) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 19.77/3.00      | v2_struct_0(X0_48) = iProver_top
% 19.77/3.00      | v2_struct_0(sK2) = iProver_top
% 19.77/3.00      | v2_struct_0(sK3) = iProver_top
% 19.77/3.00      | v2_struct_0(sK1) = iProver_top
% 19.77/3.00      | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) != iProver_top
% 19.77/3.00      | v1_funct_1(sK5) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK2) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK1) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK2) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK1) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_13378,c_806]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_12845,plain,
% 19.77/3.00      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,X1_48,X0_48,k3_tmap_1(sK2,sK1,sK2,X1_48,sK5)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
% 19.77/3.00      | v1_funct_2(k3_tmap_1(sK2,sK1,sK2,X1_48,sK5),u1_struct_0(X1_48),u1_struct_0(sK1)) != iProver_top
% 19.77/3.00      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.77/3.00      | m1_subset_1(k3_tmap_1(sK2,sK1,sK2,X1_48,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_48),u1_struct_0(sK1)))) != iProver_top
% 19.77/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X1_48,sK2) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,sK2) != iProver_top
% 19.77/3.00      | v2_struct_0(X0_48) = iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | v2_struct_0(sK2) = iProver_top
% 19.77/3.00      | v2_struct_0(sK1) = iProver_top
% 19.77/3.00      | v1_funct_1(k3_tmap_1(sK2,sK1,sK2,X1_48,sK5)) != iProver_top
% 19.77/3.00      | v1_funct_1(sK5) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK2) != iProver_top
% 19.77/3.00      | l1_pre_topc(sK1) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK2) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK1) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_12837,c_806]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_1168,plain,
% 19.77/3.00      ( ~ m1_pre_topc(X0_48,X1_48)
% 19.77/3.00      | ~ m1_pre_topc(X1_48,sK2)
% 19.77/3.00      | m1_pre_topc(X0_48,sK2)
% 19.77/3.00      | ~ l1_pre_topc(sK2)
% 19.77/3.00      | ~ v2_pre_topc(sK2) ),
% 19.77/3.00      inference(instantiation,[status(thm)],[c_312]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_1169,plain,
% 19.77/3.00      ( m1_pre_topc(X0_48,X1_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X1_48,sK2) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,sK2) = iProver_top
% 19.77/3.00      | l1_pre_topc(sK2) != iProver_top
% 19.77/3.00      | v2_pre_topc(sK2) != iProver_top ),
% 19.77/3.00      inference(predicate_to_equality,[status(thm)],[c_1168]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_34695,plain,
% 19.77/3.00      ( v1_funct_1(k3_tmap_1(sK2,sK1,sK2,X1_48,sK5)) != iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | v2_struct_0(X0_48) = iProver_top
% 19.77/3.00      | m1_subset_1(k3_tmap_1(sK2,sK1,sK2,X1_48,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_48),u1_struct_0(sK1)))) != iProver_top
% 19.77/3.00      | r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,X1_48,X0_48,k3_tmap_1(sK2,sK1,sK2,X1_48,sK5)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
% 19.77/3.00      | v1_funct_2(k3_tmap_1(sK2,sK1,sK2,X1_48,sK5),u1_struct_0(X1_48),u1_struct_0(sK1)) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X1_48,sK2) != iProver_top ),
% 19.77/3.00      inference(global_propositional_subsumption,
% 19.77/3.00                [status(thm)],
% 19.77/3.00                [c_12845,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_43,c_44,
% 19.77/3.00                 c_45,c_1092,c_1169,c_1297]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_34696,plain,
% 19.77/3.00      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,X1_48,X0_48,k3_tmap_1(sK2,sK1,sK2,X1_48,sK5)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
% 19.77/3.00      | v1_funct_2(k3_tmap_1(sK2,sK1,sK2,X1_48,sK5),u1_struct_0(X1_48),u1_struct_0(sK1)) != iProver_top
% 19.77/3.00      | m1_subset_1(k3_tmap_1(sK2,sK1,sK2,X1_48,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_48),u1_struct_0(sK1)))) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 19.77/3.00      | m1_pre_topc(X1_48,sK2) != iProver_top
% 19.77/3.00      | v2_struct_0(X1_48) = iProver_top
% 19.77/3.00      | v2_struct_0(X0_48) = iProver_top
% 19.77/3.00      | v1_funct_1(k3_tmap_1(sK2,sK1,sK2,X1_48,sK5)) != iProver_top ),
% 19.77/3.00      inference(renaming,[status(thm)],[c_34695]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_34702,plain,
% 19.77/3.00      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
% 19.77/3.00      | v1_funct_2(k3_tmap_1(sK2,sK1,sK2,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 19.77/3.00      | m1_subset_1(k3_tmap_1(sK2,sK1,sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 19.77/3.00      | m1_pre_topc(X0_48,sK3) != iProver_top
% 19.77/3.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 19.77/3.00      | v2_struct_0(X0_48) = iProver_top
% 19.77/3.00      | v2_struct_0(sK3) = iProver_top
% 19.77/3.00      | v1_funct_1(k3_tmap_1(sK2,sK1,sK2,sK3,sK5)) != iProver_top ),
% 19.77/3.00      inference(superposition,[status(thm)],[c_4665,c_34696]) ).
% 19.77/3.00  
% 19.77/3.00  cnf(c_34706,plain,
% 19.77/3.00      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
% 19.77/3.00      | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 19.77/3.01      | m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 19.77/3.01      | m1_pre_topc(X0_48,sK3) != iProver_top
% 19.77/3.01      | m1_pre_topc(sK3,sK2) != iProver_top
% 19.77/3.01      | v2_struct_0(X0_48) = iProver_top
% 19.77/3.01      | v2_struct_0(sK3) = iProver_top
% 19.77/3.01      | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) != iProver_top ),
% 19.77/3.01      inference(light_normalisation,[status(thm)],[c_34702,c_4665]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_35966,plain,
% 19.77/3.01      ( v2_struct_0(X0_48) = iProver_top
% 19.77/3.01      | r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
% 19.77/3.01      | m1_pre_topc(X0_48,sK3) != iProver_top ),
% 19.77/3.01      inference(global_propositional_subsumption,
% 19.77/3.01                [status(thm)],
% 19.77/3.01                [c_13382,c_29,c_30,c_31,c_32,c_33,c_34,c_36,c_37,c_38,
% 19.77/3.01                 c_41,c_43,c_44,c_45,c_3808,c_3809,c_3810,c_34706]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_35967,plain,
% 19.77/3.01      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
% 19.77/3.01      | m1_pre_topc(X0_48,sK3) != iProver_top
% 19.77/3.01      | v2_struct_0(X0_48) = iProver_top ),
% 19.77/3.01      inference(renaming,[status(thm)],[c_35966]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_35973,plain,
% 19.77/3.01      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4)) = iProver_top
% 19.77/3.01      | m1_pre_topc(sK4,sK3) != iProver_top
% 19.77/3.01      | v2_struct_0(sK4) = iProver_top ),
% 19.77/3.01      inference(superposition,[status(thm)],[c_10203,c_35967]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_17,negated_conjecture,
% 19.77/3.01      ( m1_pre_topc(sK4,sK0) ),
% 19.77/3.01      inference(cnf_transformation,[],[f59]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_305,negated_conjecture,
% 19.77/3.01      ( m1_pre_topc(sK4,sK0) ),
% 19.77/3.01      inference(subtyping,[status(esa)],[c_17]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_814,plain,
% 19.77/3.01      ( m1_pre_topc(sK4,sK0) = iProver_top ),
% 19.77/3.01      inference(predicate_to_equality,[status(thm)],[c_305]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_9945,plain,
% 19.77/3.01      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3))
% 19.77/3.01      | m1_pre_topc(sK3,sK0) != iProver_top
% 19.77/3.01      | m1_pre_topc(sK4,sK3) != iProver_top
% 19.77/3.01      | v2_struct_0(sK0) = iProver_top
% 19.77/3.01      | l1_pre_topc(sK0) != iProver_top
% 19.77/3.01      | v2_pre_topc(sK0) != iProver_top ),
% 19.77/3.01      inference(superposition,[status(thm)],[c_814,c_9938]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_9952,plain,
% 19.77/3.01      ( k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
% 19.77/3.01      | m1_pre_topc(sK3,sK0) != iProver_top
% 19.77/3.01      | m1_pre_topc(sK4,sK3) != iProver_top
% 19.77/3.01      | v2_struct_0(sK0) = iProver_top
% 19.77/3.01      | l1_pre_topc(sK0) != iProver_top
% 19.77/3.01      | v2_pre_topc(sK0) != iProver_top ),
% 19.77/3.01      inference(light_normalisation,[status(thm)],[c_9945,c_6188]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_12666,plain,
% 19.77/3.01      ( k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
% 19.77/3.01      inference(global_propositional_subsumption,
% 19.77/3.01                [status(thm)],
% 19.77/3.01                [c_9952,c_29,c_30,c_31,c_38,c_42]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_3209,plain,
% 19.77/3.01      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK2,sK4,sK5)
% 19.77/3.01      | m1_pre_topc(sK2,sK0) != iProver_top
% 19.77/3.01      | m1_pre_topc(sK4,sK2) != iProver_top
% 19.77/3.01      | v2_struct_0(sK0) = iProver_top
% 19.77/3.01      | l1_pre_topc(sK0) != iProver_top
% 19.77/3.01      | v2_pre_topc(sK0) != iProver_top ),
% 19.77/3.01      inference(superposition,[status(thm)],[c_814,c_3202]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_2779,plain,
% 19.77/3.01      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK2,sK1,sK5,sK4) ),
% 19.77/3.01      inference(superposition,[status(thm)],[c_2498,c_2772]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_3217,plain,
% 19.77/3.01      ( k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_tmap_1(sK2,sK1,sK5,sK4)
% 19.77/3.01      | m1_pre_topc(sK2,sK0) != iProver_top
% 19.77/3.01      | m1_pre_topc(sK4,sK2) != iProver_top
% 19.77/3.01      | v2_struct_0(sK0) = iProver_top
% 19.77/3.01      | l1_pre_topc(sK0) != iProver_top
% 19.77/3.01      | v2_pre_topc(sK0) != iProver_top ),
% 19.77/3.01      inference(light_normalisation,[status(thm)],[c_3209,c_2779]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_1615,plain,
% 19.77/3.01      ( m1_pre_topc(X0_48,sK2)
% 19.77/3.01      | ~ m1_pre_topc(X0_48,sK3)
% 19.77/3.01      | ~ m1_pre_topc(sK3,sK2)
% 19.77/3.01      | ~ l1_pre_topc(sK2)
% 19.77/3.01      | ~ v2_pre_topc(sK2) ),
% 19.77/3.01      inference(instantiation,[status(thm)],[c_1168]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_1824,plain,
% 19.77/3.01      ( ~ m1_pre_topc(sK3,sK2)
% 19.77/3.01      | m1_pre_topc(sK4,sK2)
% 19.77/3.01      | ~ m1_pre_topc(sK4,sK3)
% 19.77/3.01      | ~ l1_pre_topc(sK2)
% 19.77/3.01      | ~ v2_pre_topc(sK2) ),
% 19.77/3.01      inference(instantiation,[status(thm)],[c_1615]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_1825,plain,
% 19.77/3.01      ( m1_pre_topc(sK3,sK2) != iProver_top
% 19.77/3.01      | m1_pre_topc(sK4,sK2) = iProver_top
% 19.77/3.01      | m1_pre_topc(sK4,sK3) != iProver_top
% 19.77/3.01      | l1_pre_topc(sK2) != iProver_top
% 19.77/3.01      | v2_pre_topc(sK2) != iProver_top ),
% 19.77/3.01      inference(predicate_to_equality,[status(thm)],[c_1824]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_3930,plain,
% 19.77/3.01      ( k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_tmap_1(sK2,sK1,sK5,sK4) ),
% 19.77/3.01      inference(global_propositional_subsumption,
% 19.77/3.01                [status(thm)],
% 19.77/3.01                [c_3217,c_29,c_30,c_31,c_36,c_41,c_42,c_1092,c_1297,
% 19.77/3.01                 c_1825]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_11,negated_conjecture,
% 19.77/3.01      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
% 19.77/3.01      inference(cnf_transformation,[],[f65]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_311,negated_conjecture,
% 19.77/3.01      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
% 19.77/3.01      inference(subtyping,[status(esa)],[c_11]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_808,plain,
% 19.77/3.01      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) != iProver_top ),
% 19.77/3.01      inference(predicate_to_equality,[status(thm)],[c_311]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_3806,plain,
% 19.77/3.01      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) != iProver_top ),
% 19.77/3.01      inference(demodulation,[status(thm)],[c_3804,c_808]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_3932,plain,
% 19.77/3.01      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,sK4)) != iProver_top ),
% 19.77/3.01      inference(demodulation,[status(thm)],[c_3930,c_3806]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_12668,plain,
% 19.77/3.01      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4)) != iProver_top ),
% 19.77/3.01      inference(demodulation,[status(thm)],[c_12666,c_3932]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_18,negated_conjecture,
% 19.77/3.01      ( ~ v2_struct_0(sK4) ),
% 19.77/3.01      inference(cnf_transformation,[],[f58]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(c_39,plain,
% 19.77/3.01      ( v2_struct_0(sK4) != iProver_top ),
% 19.77/3.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.77/3.01  
% 19.77/3.01  cnf(contradiction,plain,
% 19.77/3.01      ( $false ),
% 19.77/3.01      inference(minisat,[status(thm)],[c_35973,c_12668,c_42,c_39]) ).
% 19.77/3.01  
% 19.77/3.01  
% 19.77/3.01  % SZS output end CNFRefutation for theBenchmark.p
% 19.77/3.01  
% 19.77/3.01  ------                               Statistics
% 19.77/3.01  
% 19.77/3.01  ------ General
% 19.77/3.01  
% 19.77/3.01  abstr_ref_over_cycles:                  0
% 19.77/3.01  abstr_ref_under_cycles:                 0
% 19.77/3.01  gc_basic_clause_elim:                   0
% 19.77/3.01  forced_gc_time:                         0
% 19.77/3.01  parsing_time:                           0.012
% 19.77/3.01  unif_index_cands_time:                  0.
% 19.77/3.01  unif_index_add_time:                    0.
% 19.77/3.01  orderings_time:                         0.
% 19.77/3.01  out_proof_time:                         0.028
% 19.77/3.01  total_time:                             2.288
% 19.77/3.01  num_of_symbols:                         53
% 19.77/3.01  num_of_terms:                           57558
% 19.77/3.01  
% 19.77/3.01  ------ Preprocessing
% 19.77/3.01  
% 19.77/3.01  num_of_splits:                          0
% 19.77/3.01  num_of_split_atoms:                     0
% 19.77/3.01  num_of_reused_defs:                     0
% 19.77/3.01  num_eq_ax_congr_red:                    31
% 19.77/3.01  num_of_sem_filtered_clauses:            1
% 19.77/3.01  num_of_subtypes:                        5
% 19.77/3.01  monotx_restored_types:                  0
% 19.77/3.01  sat_num_of_epr_types:                   0
% 19.77/3.01  sat_num_of_non_cyclic_types:            0
% 19.77/3.01  sat_guarded_non_collapsed_types:        0
% 19.77/3.01  num_pure_diseq_elim:                    0
% 19.77/3.01  simp_replaced_by:                       0
% 19.77/3.01  res_preprocessed:                       102
% 19.77/3.01  prep_upred:                             0
% 19.77/3.01  prep_unflattend:                        0
% 19.77/3.01  smt_new_axioms:                         0
% 19.77/3.01  pred_elim_cands:                        8
% 19.77/3.01  pred_elim:                              0
% 19.77/3.01  pred_elim_cl:                           0
% 19.77/3.01  pred_elim_cycles:                       1
% 19.77/3.01  merged_defs:                            0
% 19.77/3.01  merged_defs_ncl:                        0
% 19.77/3.01  bin_hyper_res:                          0
% 19.77/3.01  prep_cycles:                            3
% 19.77/3.01  pred_elim_time:                         0.
% 19.77/3.01  splitting_time:                         0.
% 19.77/3.01  sem_filter_time:                        0.
% 19.77/3.01  monotx_time:                            0.
% 19.77/3.01  subtype_inf_time:                       0.001
% 19.77/3.01  
% 19.77/3.01  ------ Problem properties
% 19.77/3.01  
% 19.77/3.01  clauses:                                29
% 19.77/3.01  conjectures:                            18
% 19.77/3.01  epr:                                    19
% 19.77/3.01  horn:                                   22
% 19.77/3.01  ground:                                 18
% 19.77/3.01  unary:                                  18
% 19.77/3.01  binary:                                 1
% 19.77/3.01  lits:                                   123
% 19.77/3.01  lits_eq:                                2
% 19.77/3.01  fd_pure:                                0
% 19.77/3.01  fd_pseudo:                              0
% 19.77/3.01  fd_cond:                                0
% 19.77/3.01  fd_pseudo_cond:                         0
% 19.77/3.01  ac_symbols:                             0
% 19.77/3.01  
% 19.77/3.01  ------ Propositional Solver
% 19.77/3.01  
% 19.77/3.01  prop_solver_calls:                      28
% 19.77/3.01  prop_fast_solver_calls:                 4484
% 19.77/3.01  smt_solver_calls:                       0
% 19.77/3.01  smt_fast_solver_calls:                  0
% 19.77/3.01  prop_num_of_clauses:                    14795
% 19.77/3.01  prop_preprocess_simplified:             34235
% 19.77/3.01  prop_fo_subsumed:                       1754
% 19.77/3.01  prop_solver_time:                       0.
% 19.77/3.01  smt_solver_time:                        0.
% 19.77/3.01  smt_fast_solver_time:                   0.
% 19.77/3.01  prop_fast_solver_time:                  0.
% 19.77/3.01  prop_unsat_core_time:                   0.004
% 19.77/3.01  
% 19.77/3.01  ------ QBF
% 19.77/3.01  
% 19.77/3.01  qbf_q_res:                              0
% 19.77/3.01  qbf_num_tautologies:                    0
% 19.77/3.01  qbf_prep_cycles:                        0
% 19.77/3.01  
% 19.77/3.01  ------ BMC1
% 19.77/3.01  
% 19.77/3.01  bmc1_current_bound:                     -1
% 19.77/3.01  bmc1_last_solved_bound:                 -1
% 19.77/3.01  bmc1_unsat_core_size:                   -1
% 19.77/3.01  bmc1_unsat_core_parents_size:           -1
% 19.77/3.01  bmc1_merge_next_fun:                    0
% 19.77/3.01  bmc1_unsat_core_clauses_time:           0.
% 19.77/3.01  
% 19.77/3.01  ------ Instantiation
% 19.77/3.01  
% 19.77/3.01  inst_num_of_clauses:                    4363
% 19.77/3.01  inst_num_in_passive:                    1600
% 19.77/3.01  inst_num_in_active:                     1381
% 19.77/3.01  inst_num_in_unprocessed:                1382
% 19.77/3.01  inst_num_of_loops:                      1710
% 19.77/3.01  inst_num_of_learning_restarts:          0
% 19.77/3.01  inst_num_moves_active_passive:          326
% 19.77/3.01  inst_lit_activity:                      0
% 19.77/3.01  inst_lit_activity_moves:                1
% 19.77/3.01  inst_num_tautologies:                   0
% 19.77/3.01  inst_num_prop_implied:                  0
% 19.77/3.01  inst_num_existing_simplified:           0
% 19.77/3.01  inst_num_eq_res_simplified:             0
% 19.77/3.01  inst_num_child_elim:                    0
% 19.77/3.01  inst_num_of_dismatching_blockings:      5345
% 19.77/3.01  inst_num_of_non_proper_insts:           4531
% 19.77/3.01  inst_num_of_duplicates:                 0
% 19.77/3.01  inst_inst_num_from_inst_to_res:         0
% 19.77/3.01  inst_dismatching_checking_time:         0.
% 19.77/3.01  
% 19.77/3.01  ------ Resolution
% 19.77/3.01  
% 19.77/3.01  res_num_of_clauses:                     0
% 19.77/3.01  res_num_in_passive:                     0
% 19.77/3.01  res_num_in_active:                      0
% 19.77/3.01  res_num_of_loops:                       105
% 19.77/3.01  res_forward_subset_subsumed:            70
% 19.77/3.01  res_backward_subset_subsumed:           0
% 19.77/3.01  res_forward_subsumed:                   0
% 19.77/3.01  res_backward_subsumed:                  0
% 19.77/3.01  res_forward_subsumption_resolution:     0
% 19.77/3.01  res_backward_subsumption_resolution:    0
% 19.77/3.01  res_clause_to_clause_subsumption:       1344
% 19.77/3.01  res_orphan_elimination:                 0
% 19.77/3.01  res_tautology_del:                      179
% 19.77/3.01  res_num_eq_res_simplified:              0
% 19.77/3.01  res_num_sel_changes:                    0
% 19.77/3.01  res_moves_from_active_to_pass:          0
% 19.77/3.01  
% 19.77/3.01  ------ Superposition
% 19.77/3.01  
% 19.77/3.01  sup_time_total:                         0.
% 19.77/3.01  sup_time_generating:                    0.
% 19.77/3.01  sup_time_sim_full:                      0.
% 19.77/3.01  sup_time_sim_immed:                     0.
% 19.77/3.01  
% 19.77/3.01  sup_num_of_clauses:                     513
% 19.77/3.01  sup_num_in_active:                      314
% 19.77/3.01  sup_num_in_passive:                     199
% 19.77/3.01  sup_num_of_loops:                       340
% 19.77/3.01  sup_fw_superposition:                   340
% 19.77/3.01  sup_bw_superposition:                   265
% 19.77/3.01  sup_immediate_simplified:               199
% 19.77/3.01  sup_given_eliminated:                   3
% 19.77/3.01  comparisons_done:                       0
% 19.77/3.01  comparisons_avoided:                    0
% 19.77/3.01  
% 19.77/3.01  ------ Simplifications
% 19.77/3.01  
% 19.77/3.01  
% 19.77/3.01  sim_fw_subset_subsumed:                 30
% 19.77/3.01  sim_bw_subset_subsumed:                 10
% 19.77/3.01  sim_fw_subsumed:                        18
% 19.77/3.01  sim_bw_subsumed:                        3
% 19.77/3.01  sim_fw_subsumption_res:                 0
% 19.77/3.01  sim_bw_subsumption_res:                 0
% 19.77/3.01  sim_tautology_del:                      3
% 19.77/3.01  sim_eq_tautology_del:                   7
% 19.77/3.01  sim_eq_res_simp:                        0
% 19.77/3.01  sim_fw_demodulated:                     9
% 19.77/3.01  sim_bw_demodulated:                     24
% 19.77/3.01  sim_light_normalised:                   204
% 19.77/3.01  sim_joinable_taut:                      0
% 19.77/3.01  sim_joinable_simp:                      0
% 19.77/3.01  sim_ac_normalised:                      0
% 19.77/3.01  sim_smt_subsumption:                    0
% 19.77/3.01  
%------------------------------------------------------------------------------
